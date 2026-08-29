% This file is part of the ABALearn project.
% Copyright (C) 2023, 2024 The ABALearn's Authors

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

:- module(asp_utils,
    [  asp/7
    ,  dump_rule/1
    ,  dump_rules/1
    ,  dump_rules/2
    ,  new_rule/3
    ,  normalize_args/3
    ,  read_bk/2
    ,  bksize/1
    ,  rules_aba_utl/2
    ,  aba_rules/2
    ,  aba_p_rules/2
    ,  aba_p_rules_append/3
    ,  aba_p_rules_replace/3
    ,  aba_p_rules_select/3
    ,  aba_p_rules_member/2
    ,  aba_p_rules_memberchk/2    
    ,  aba_ni_rules/2
    ,  aba_ni_rules_append/3
    ,  aba_ni_rules_replace/3
    ,  aba_ni_rules_select/3
    ,  aba_ni_rules_member/2
    ,  aba_asms/2
    ,  aba_asms_append/3
    ,  aba_asms_replace/3
    ,  aba_asms_select/3
    ,  aba_asms_member/2
    ,  aba_cnts/2
    ,  aba_cnts_append/3
    ,  aba_cnts_replace/3
    ,  aba_cnts_select/3
    ,  aba_cnts_member/2
    ,  utl_rules/2
    ,  utl_rules_append/3
    ,  utl_rules_replace/3
    ,  utl_rules_select/3
    ,  utl_rules_member/2
    ,  utl_rules_memberchk/2    
    ,  consts_in_BK/3
    ,  show_rule/1
    ,  show_term/1
    ,  set_semantics_enc/0
    ,  op(300,fy,not)
    ,  rlid/1
    ,  ic/2
    ,  bk_preds/1
    ,  update_fwt/3
    ,  ftw_term_key/2
    ,  ftw_key_ids/3
    ,  is_rule/1
    ,  rule_id/2
    ,  rule_hd/2
    ,  rule_bd/2
    ]).

:- use_module(library(dialect/hprolog),
    [ memberchk_eq/2 ]).

:- use_module(library(clpfd)).

:- dynamic rid/1.

:- dynamic rlid/1.

:- dynamic bk_preds/1.

:- dynamic bksize/1.

:- dynamic asp/7.

:- initialization(
  assert( ( 
    asp(Ri,Ep0,En0,Ep,En,Ps, Ro) :-
      native_asp_enc(Ri,Ep0,En0,Ep,En,Ps, Ro)
    ) 
  )
).

set_semantics_enc :-
  retractall(asp(_,_,_,_,_,_,_)),
  assert( ( 
    asp(Ri,Ep0,En0,Ep,En,Ps, Ro) :-
      tjm_asp_enc(Ri,Ep0,En0,Ep,En,Ps, Ro)
    ) 
  ).  

% rule_id(I): I is a fresh new rule identifier 
rule_id(I) :-
  retract(rid(I)),
  I1 is I+1,
  assert(rid(I1)).

% new_rule(H,B, R): R is the term representing
% a rule whose head is H and body is B
new_rule(H,B, R) :-
  ( is_list(B) -> true; throw(new_rule:not_a_list(B)) ),
  rule_id(I),
  normalize_atom(H, HN,HE), 
  %split_body(B,C,U), constr(C,C1),
  B=U,
  normalize_eqs(U, BE,A),
  normalize_atoms(A,BE, A1,BE1),
  append(HE,BE1,E),
  single_constant(E,E1),
  append(E1,A1,B1),
  rule_id(R,I), rule_hd(R,HN), rule_bd(R,B1).
% new_rule/3 utility predicate
% normalize_atom/3
normalize_atom(H, H1,B) :-
  H  =.. [P|A],
  normalize_args(A, N,B),
  H1 =.. [P|N].
% normalize_atoms/2 
normalize_atoms([],E, [],E).
normalize_atoms([A1|A1s],E1, [A2|A2s],E4) :-
  normalize_atom(A1, A2,E2),
  append(E2,E1,E3),
  normalize_atoms(A1s,E3, A2s,E4).
% normalize_args/3
normalize_args([], [],[]).
normalize_args([C|As], [V|Vs],[V=C|Bs]) :-
  atomic(C),
  !,
  normalize_args(As, Vs,Bs).
normalize_args([A|As], [A|Vs],Bs) :-
  normalize_args(As, Vs,Bs).
% normalize_eqs/3
normalize_eqs([],[],[]).
normalize_eqs([V=C|L], [V=C|Es],As) :-
  var(V),
  ground(C),
  !,
  normalize_eqs(L, Es,As).
normalize_eqs([C=V|L], [V=C|Es],As) :-
  ground(C),
  var(V),
  !,
  normalize_eqs(L,Es,As).
normalize_eqs([V1=V2|L], Es,As) :-
  var(V1),
  var(V2),
  !,
  V1=V2,
  normalize_eqs(L, Es,As).
normalize_eqs([A|L], Es,[A|As]):-
  normalize_eqs(L, Es,As).
% normalize_body/3
normalize_body(B, B1) :-
  normalize_eqs(B, E1,A),
  normalize_atoms(A, A1),
  append(E1,A1,B1).
% single_constant
single_constant([],[]).
single_constant([V1=C|E1],E2) :-
  select(V2=C,E1,R1),
  V1=V2,
  !,
  single_constant([V1=C|R1],E2).
single_constant([V1=C|E1],[V1=C|E2]) :-
  single_constant(E1,E2).  

%
split_body([],[],[]).
split_body([C|As],[C1|Cs],Bs) :-
  C =.. [F,A1,A2],
  memberchk(F,[#>=,#=<,#=,:=,#>,#<]),
  !,
  normalize_constr(F,A1,A2,C1),
  split_body(As,Cs,Bs).
split_body([A|As],Cs,[A|Bs]) :-
  split_body(As,Cs,Bs).  

%
normalize_constr(F,A1,A2, C) :-
  memberchk(F,[#>=,#=<,#=,:=]),
  !,
  normalize_constr_aux(A1,A2, N1,N2),
  C =.. [F,N1,N2]. 
normalize_constr(F,A1,A2, C) :-
  F == #>,
  !,
  normalize_constr_aux(A1,A2, N1,N2),
  N3 is N2+1,
  C =.. [#>=,N1,N3].
normalize_constr(F,A1,A2, C) :-
  F == #<,
  !,
  normalize_constr_aux(A1,A2, N1,N2),
  N3 is N2-1,
  C =.. [#=<,N1,N3].  
  
%
normalize_constr_aux(A1,A2, A1,A2) :-
  var(A1), !.  
normalize_constr_aux(A1,A2, A2,A1).

%
constr([],[]) :-
  !.
constr(C,S) :-
  term_variables(C,V), length(V,N), length(S,N), pairs(V,S), constr_aux(C,S).

%
constr_aux([],_).
constr_aux([V#>=C|Cs],S) :-
  member(c(V1,L,_),S),
  V == V1,
  !,
  L = C,
  constr_aux(Cs,S).
constr_aux([V#=<C|Cs],S) :-
  member(c(V1,_,U),S),
  V == V1,
  !,
  U = C,
  constr_aux(Cs,S). 
constr_aux([V#=C|Cs],S) :-
  member(c(V1,L,U),S),
  V == V1,
  !,
  U = C, L = C,
  constr_aux(Cs,S).
constr_aux([V:=C|Cs],S) :-
  member(c(V1,L,U),S),
  V == V1,
  !,
  U = C, L = C,
  constr_aux(Cs,S).    

pairs([],[]).
pairs([V|Vs],[c(V,_,_)|S]) :-
  pairs(Vs,S).

% new_asp_rule(H,B, R): R is the term representing
% an asp rule whose head is H and body is B
new_asp_rule(H,B, R) :-
  ( is_list(B) -> true; throw(new_rule:not_a_list(B)) ),
  R = asp_rule(H,B).

%
rules_aba_utl(Rs, AE) :-
  findall(R1, (member(R1,Rs),functor(R1,rule,3)), R),
  findall(R2, (member(R2,Rs),functor(R2,assumption,1)), A),
  findall(R3, (member(R3,Rs),functor(R3,contrary,2)), C),
  % generate asm_cnt_dom/3 facts from rules
  generate_asm_cnt_dom1(R,A,C,[],no, ACD1,FlagI),
  % generate asm_cnt_dom/3 facts for assumption not occuring in rules  
  generate_asm_cnt_dom2(C,ACD1,FlagI, ACD2,FlagO),
  % generate dom/1 facts if there exists an assumption of the native encoding using it, or
  % you are using the tjm encoding (semantics/1 holds)
  ( ( FlagO == yes ; lopt(semantics(_)) ) ->
    ( consts_in_BK(R,[], Cs), findall(dr(dom(C1)), member(C1,Cs), DRs) )
  ;
    true
  ),
  %
  append(ACD2,DRs,Us),
  update_fwt(R, aba_enc(R,[],A,C,[fwt([])|Us]), AE).
  
%
generate_asm_cnt_dom1([],_,_,F,Flag, F,Flag).
generate_asm_cnt_dom1([R|Rs],A,C,Fi,FlagI, Fo,FlagO) :- 
  rule_bd(R,BwA), 
  body_asms(BwA,A, As,Ps),
  As \= [],
  !,
  generate_asm_cnt_dom1_aux(As,C,Ps,Fi,FlagI, Fi1,FlagI1),
  generate_asm_cnt_dom1(Rs,A,C,Fi1,FlagI1, Fo,FlagO).
generate_asm_cnt_dom1([_|Rs],A,C,Fi,FlagI, Fo,FlagO) :- 
  generate_asm_cnt_dom1(Rs,A,C,Fi,FlagI, Fo,FlagO).  
%
generate_asm_cnt_dom1_aux([],_,_,F,Flag, F,Flag).
generate_asm_cnt_dom1_aux([A|As],Cs,Ps,Fi,FlagI, Fo,FlagO) :-
  member(contrary(A,C_A),Cs),
  copy_term((A,C_A,Ps),(A1,C_A1,Ps1)),
  term_variables(A1, Vars),
  term_variables(Ps1, PsVars),    
  domains_of(Vars,PsVars,FlagI, B1,FlagI1),
  append(B1,Ps1,B2),
  ACD = asm_cnt_dom(A1,C_A1,B2),
  ( ( member(F,Fi), variant(F,ACD) ) -> Fi1 = Fi ; Fi1 = [ACD|Fi] ),  
  generate_asm_cnt_dom1_aux(As,Cs,Ps,Fi1,FlagI1, Fo,FlagO).

%
body_asms([],_, [],[]). 
body_asms([A|B],C, [A|As],Ps) :-
  member(assumption(A),C),
  !,
  body_asms(B,C, As,Ps).
body_asms([P|B],C, As,[P|Ps]) :-
  body_asms(B,C, As,Ps).  

%
generate_asm_cnt_dom2([],AD,Flag, AD,Flag).
generate_asm_cnt_dom2([contrary(Alpha,_)|Cs],AD,FlagI, AD1,FlagO) :-
  copy_term(Alpha,Alpha1),
  memberchk(asm_cnt_dom(Alpha1,_,_),AD),
  !,
  generate_asm_cnt_dom2(Cs,AD,FlagI, AD1,FlagO).
generate_asm_cnt_dom2([contrary(Alpha,C_Alpha)|Cs],AD,_FlagI, [asm_cnt_dom(Alpha1,C_Alpha1,B1)|AD1],FlagO) :-
  copy_term(contrary(Alpha,C_Alpha),contrary(Alpha1,C_Alpha1)),
  !,
  term_variables(Alpha1,Vars),
  domains_of(Vars, B1),
  generate_asm_cnt_dom2(Cs,AD,yes, AD1,FlagO).
  

% update_fwt(+ABA1,+Rs, ABA2)
update_fwt(Rs,aba_enc(R,N,A,C,U1), aba_enc(R,N,A,C,[fwt(FwT2)|U2])) :-
  select(fwt(FwT1),U1, U2),
  update_fwt_list(Rs,FwT1, FwT2).

% update_fwt_list(+Rs,+FwTI, -FwTO)
update_fwt_list([],FwT, FwT).
update_fwt_list([R|Rs],FwTI, FwTO) :-
  rule_id(R,I), rule_bd(R,As),
  update_fwt(I,As,FwTI, FwTI1),
  !,
  update_fwt_list(Rs,FwTI1, FwTO).

% update_fwt(+I,+As,+FwTI, -FwTO)
% add the identifier I of the rule having in the body the atoms As to the table FwTI
update_fwt(_,[],FwT, FwT).
update_fwt(I,[A|As],FwTI, FwTO) :-
  ftw_term_key(A, P/N),
  add_item_ftw(P/N,I,FwTI, FwTI1),
  !,
  update_fwt(I,As,FwTI1, FwTO).  

%
ftw_term_key(X=Y, P/N) :-
  var(X), ground(Y),
  !,
  functor(Y,P,N).
ftw_term_key(X=Y, P/N) :-
  var(Y), ground(X),
  !,
  functor(Y,P,N).
ftw_term_key(A, P/N) :-
  functor(A,P,N).

%
add_item_ftw(P/N,I,FwTI, FwTO) :-
  select((P/N,Is),FwTI, FwTI1),
  !,
  append(Is,[I],Is1),
  FwTO = [(P/N,Is1)|FwTI1].
add_item_ftw(P/N,I,FwTI, [(P/N,[I])|FwTI]).

%
ftw_key_ids(P/N,[T|Ts],I) :-
  ftw_key_ids_aux(P/N,[T|Ts],I),
  !.
ftw_key_ids(K,FwT,I) :- 
  abalearn_error((write('ftw_key_ids: wrong arguments: '), write(ftw_key_ids(K,FwT,I)))).
%
ftw_key_ids_aux(P/N,FwT,I) :-  
  memberchk((P/N,I),FwT).
ftw_key_ids_aux(_,_,[]).

% read_bk(+File, -Rules):
% read a read of rules of from File and
% generate a list of rule/3 terms representing them.
read_bk(FileName, Rules) :-
  % initialize rule identifier
  retractall(rid(_)),
  assert(rid(1)),
  ( open_bkfile(FileName, Stream) -> read_bk_aux(Stream, Rules) ; fail ),
  rid(ID),
  retractall(rlid(_)),  
  assert(rlid(ID)), % ID of the first learnt rule
  close(Stream),
  retractall(bksize(_)),
  BKSize is ID-1, 
  assert(bksize(BKSize)),
  preds_in_BK(Rules).
%
open_bkfile(FileName, Stream) :-
  FileName = File,
  catch( open(File, read, Stream),
    error(existence_error(source_sink,_),_),
    ( write('WARNING: '), write(File), write(' not found -- trying adding .aba extension'), nl, fail ) 
  ),
  !.
open_bkfile(FileName, Stream) :-
  atom_concat(FileName,'.aba',File),
  catch( open(File, read, Stream),
    error(existence_error(source_sink,_),_),
    ( write('ERROR: neither '), write(FileName), write(' nor '), write(File), write(' was found!'), nl, fail ) 
  ).

% read_bk/2 utility predicate: 
% read all terms from Stream and
% generate the corresponding rule/3 terms
read_bk_aux(Stream, [R|Rs]) :-
  read(Stream,Term),
  Term \== end_of_file,
  !,
  bk_term(Term,R),
  read_bk_aux(Stream, Rs).
read_bk_aux(_, []).
%
bk_term(Term, R) :-
  Term = ( Head :- Body ),
  !,
  conj_to_list(Body,B),
  ( functor(Head,contrary,2) ->
    R = Head
  ; new_rule(Head,B, R)  % Head :- Body
  ).
bk_term(Term, R) :-
  ( ( functor(Term,assumption,1) ; functor(Term,feature,2) ) ->
    R = Term
  ;
    new_rule(Term,[], R) % fact
  ).

% conj_to_list(C, L): 
% C is a conjunction of the form (A1,...,An);
% L is a list of the form [A1,...,An]
conj_to_list(X,[]) :-
  X==true,
  !.
conj_to_list(B,L) :-
  ( nonvar(B), functor(B,',',_) ->
    ( B = (B1,B2), L=[B1|H], conj_to_list(B2,H) )
  ;
    L=[B]
  ).

%
preds_in_BK(Rules) :-
  preds_in_BK(Rules,P),
  sort(P,S),
  assert(bk_preds(S)).
preds_in_BK([],[]).
preds_in_BK([R|Rs],[F/N|P]) :-
  rule_hd(R,H),
  functor(H,F,N),
  !,
  preds_in_BK(Rs,P).
preds_in_BK([_|Rs],P) :-
  preds_in_BK(Rs,P).

%
consts_in_BK([],CsI, CsO) :-
  sort(CsI, CsO).
consts_in_BK([R|Rs],CsI, CsO) :-
  rule_bd(R,B),
  consts_in_bd(B,CsI,CsI1),
  !,
  consts_in_BK(Rs,CsI1, CsO).
consts_in_BK([_|Rs],CsI, CsO) :-
  consts_in_BK(Rs,CsI, CsO).
%
consts_in_bd([],Cs, Cs).
consts_in_bd([_=C|Bs],CsI, CsO) :-
  !,
  consts_in_bd(Bs,[C|CsI], CsO).
consts_in_bd([_|Bs],CsI, CsO) :-
  consts_in_bd(Bs,CsI, CsO).  
 
% SEMANTICS: writes all rules to file
dump_rules(Rs) :-
  dump_rules(Rs,'asp.clingo').
dump_rules(Rs,File) :-
  tell(File),
  aba_rules(Rs,A), utl_rules(Rs,U),
  dump_rules_aux(A),
  nl,
  dump_rules_aux(U),
  told.  
% write rules
dump_rules_aux([]).
dump_rules_aux([R|Rs]) :-
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  dump_rule(CpyR),
  dump_rules_aux(Rs).
% write rule
dump_rule(R) :-
  rule_hd(R,H), rule_bd(R,B),
  !,
  write(H),      % head of the rule
  ( B==[] ->
    ( write('.'), nl ) % fact or int. constr. 
  ;
    ( write(' :- '), write_bd(B) ) % rule w/nonempty body
  ).
dump_rule(R) :-
  R = ic(B),
  !,
  ( write(' :- '), write_bd(B) ). 
dump_rule(R) :-
  R = dr(B),
  !,
  ( write(B), write(.), nl ).   
dump_rule(R) :-
  R = directive(D,A),
  !,
  write('#'), write(D), write(' '), write(A), write('.'), nl.
dump_rule(R) :-
  functor(R,F,N),
  memberchk(F/N,[gf/1,mgr/1,fwt/1,feature/2,asm_cnt_dom/3]),
  !.
dump_rule(R) :-
  told,
  write('ERROR: unrecognized rule: '), 
  copy_term(R,CpyR),
  numbervars(CpyR,0,_), 
  write(CpyR),
  nl,
  halt.

% dump_rule/1 utility predicate
write_bd([H]) :-
  !,
  write(H), write('.'), nl.
write_bd([H|T]) :-
  write(H), write(', '),
  write_bd(T).

write_show([]).
write_show([P/N|Ps]) :-
   write('#show '), write(P/N), write('.'), nl,
  write_show(Ps).

%
ic(B, ic(B)).

% -----------------------------------------------------------------------------
% aba_enc(R,N,A,C,O)
% R list of rules
% N list of nonintensional rules (to be processed)
% A list of assumptions
% C list of contraries
% U list of utility rules
%
% aba_rules(+ABAf, O), O is the list of ABA rules in ABAf
aba_rules(aba_enc(R,N,_,_,_), O) :-
  append(R,N,O).
%
% aba_p_rules(?ABAf,?R)
% aba_p_rules_append(?ABAf1,?R,?ABAf2)
% aba_p_rules_replace(?ABAf1,?R,?ABAf2)
% aba_p_rules_select(?R,?ABAf1,?ABAf2)
% aba_p_rules_member(?R,?ABAf)
aba_p_rules(aba_enc(R,_,_,_,_),R).
aba_p_rules_append(aba_enc(R1,N,A,C,U),R, aba_enc(R2,N,A,C,U)) :-
  append(R1,R,R2).
aba_p_rules_replace(aba_enc(_,N,A,C,U),R, aba_enc(R,N,A,C,U)).
aba_p_rules_select(R,aba_enc(R1,N,A,C,U), aba_enc(R2,N,A,C,U)) :-
  select(R,R1,R2).
aba_p_rules_member(R,aba_enc(R1,_,_,_,_)) :-
  member(R,R1).
aba_p_rules_memberchk(R,aba_enc(R1,_,_,_,_)) :-
  memberchk(R,R1).
%
% aba_ni_rules(?ABAf,?N)
% aba_ni_rules_append(?ABAf1,?N,?ABAf2)
% aba_ni_rules_replace(?ABAf1,?N,?ABAf2)
% aba_ni_rules_select(?N,?ABAf1,?ABAf2)
% aba_ni_rules_member(?N,?ABAf)
aba_ni_rules(aba_enc(_,N,_,_,_),N).
aba_ni_rules_append(aba_enc(R,N1,A,C,U),N, aba_enc(R,N2,A,C,U)) :-
  append(N1,N,N2).
aba_ni_rules_replace(aba_enc(R,_,A,C,U),N, aba_enc(R,N,A,C,U)).
aba_ni_rules_select(N,aba_enc(R,N1,A,C,U), aba_enc(R,N2,A,C,U)) :-
  select(N,N1,N2).
aba_ni_rules_member(N,aba_enc(_,N1,_,_,_)) :-
  member(N,N1).
%
% aba_asms(?ABAf,?A)
% aba_asms_append(?ABAf1,?A,?ABAf2)
% aba_asms_replace(?ABAf1,?A,?ABAf2)
% aba_asms_select(?A,?ABAf1,?ABAf2)
% aba_asms_member(?A,?ABAf)
aba_asms(aba_enc(_,_,A,_,_),A).
aba_asms_append(aba_enc(R,N,A1,C,U),A, aba_enc(R,N,A2,C,U)) :-
  append(A1,A,A2).
aba_asms_replace(aba_enc(R,N,_,C,U),A, aba_enc(R,N,A,C,U)).
aba_asms_select(A,aba_enc(I,N,A1,C,U), aba_enc(I,N,A2,C,U)) :-
  select(A,A1,A2).
aba_asms_member(A, aba_enc(_,_,A1,_,_)) :-
  member(A,A1).
%
% aba_cnts(?ABAf,?C)
% aba_cnts_append(?ABAf1,?C,?ABAf2)
% aba_cnts_replace(?ABAf1,?C,?ABAf2)
% aba_cnts_select(?C,?ABAf1,?ABAf2)
% aba_cnts_member(?C,?ABAf)
aba_cnts(aba_enc(_,_,_,C,_),C).
aba_cnts_append(aba_enc(R,N,A,C1,U),C, aba_enc(R,N,A,C2,U)) :-
  append(C1,C,C2).
aba_cnts_replace(aba_enc(R,N,A,_,U),C, aba_enc(R,N,A,C,U)).
aba_cnts_select(C,aba_enc(I,N,A,C1,U), aba_enc(I,N,A,C2,U)) :-
  select(C,C1,C2).
aba_cnts_member(C, aba_enc(_,_,_,C1,_)) :-
  member(C,C1).
%
% utl_rules(?ABAf,?U)
% utl_rules_append(?ABAf1,?U,?ABAf2)
% utl_rules_replace(?ABAf1,?U,?ABAf2)
% utl_rules_select(?U,?ABAf1,?ABAf2)
% utl_rules_member(?U,?ABAf)
utl_rules(aba_enc(_,_,_,_,U), U).
utl_rules_append(aba_enc(R,N,A,C,U1),U, aba_enc(R,N,A,C,U2)) :-
  append(U1,U,U2).
utl_rules_replace(aba_enc(R,N,A,C,_),U, aba_enc(R,N,A,C,U)).
utl_rules_select(U,aba_enc(R,N,A,C,U1), aba_enc(R,N,A,C,U2)) :-
  select(U,U1,U2).
utl_rules_member(U, aba_enc(_,_,_,_,U1)) :-
  member(U,U1).
utl_rules_memberchk(U, aba_enc(_,_,_,_,U1)) :-
  memberchk(U,U1).

% is_rule
% rule_{id|hd|bd}
is_rule(R) :-
  nonvar(R),
  functor(R,rule,3).
%
rule_id(rule(I,_,_),I).
rule_hd(rule(_,H,_),H).
rule_bd(rule(_,_,B),B).

% pretty print a rule
show_rule(R) :-
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  rule_hd(CpyR,H), rule_bd(CpyR,B),
  write(H), write(' <- '), write(B).

% pretty print a term
show_term(A) :-
  copy_term(A,CpyA),
  numbervars(CpyA,0,_),
  write(CpyA).


% intersection(L1,L2,I)
% I is the intersection of L1 and L2
intersection([],_,[]).
intersection([E|L],L2,[E|L3]) :-
  memberchk_eq(E,L2),
  !,
  intersection(L,L2,L3).
intersection([_|L],L2,L3) :-
  intersection(L,L2,L3).

% -----------------------------------------------------------------------------
% native ASP encoding of Ri
native_asp_enc(Ri,Ep0,En0,Ep,En,[], Ro) :-
  !,
  % ic of the already covered examples
  ic(Ep0,En0, I1),
  utl_rules_append(Ri,I1,Ri1),
  % ic of the examples to be learnt
  ic(Ep,En, I2), 
  utl_rules_append(Ri1,I2,Ri2),
  % rules for assumptions
  asm_aux_rules(Ri2, Rs),
  utl_rules_append(Ri2,Rs,Ro).
native_asp_enc(Af,Ep0,En0,Ep,En,[P/N|Ls], ASP) :-
  functor(C,P,N), % C is the atom with functor P/N
  aba_cnts(Af, Cs), % Cs: list of contraries in the ABA framework Af
  member(contrary(A,C),Cs), % C is a contrary (i.e., it belongs to Cs)
  !, % P/N is the predicate of a contrary
  utl_rules(Af,Us), % U is the list of utility rules in Af
  member(asm_cnt_dom(A,_,B),Us), % retrieve the domain B of the assumption A 
  copy_term((C,B),(C1,B1)), % get a copy of the contrary C and its context B
  C1 =.. [P|V], % get the variables of C1
  atom_concat(P,'_P',C_P), % primed version of the predicate P
  CP1 =.. [C_P|V], % primed version of the contrary
  new_rule({CP1},B1, G), % {p_P} :- B
  new_rule(C1,[CP1], R), % p :- p_P
  copy_term(CP1,CP2),
  % TODO: add here a rule for cautious reasoning
  gi_of_cp(CP1,B1,GIofCP),
  %%%
  utl_rules_append(Af,[G,R,directive(minimize,{1,CP2:CP2}),directive(show,C_P/N)|GIofCP], Af1),
  native_asp_enc(Af1,Ep0,En0,Ep,En,Ls, ASP).
native_asp_enc(Af,Ep0,En0,Ep,En,[P/N|Ls], ASP) :-
  atom_concat(P,'_P',P_P), 
  findall(E1, ( member(E,Ep), functor(E,P,N), E =..[P|A], E1 =..[P_P|A] ), EpP), 
  EpP = [_|_], 
  !, % P/N is the predicate of at least one positive example
  ep_choice(EpP, EpG), 
  new_rule({EpG},[], G),
  length(V,N), A =.. [P|V], A_P =.. [P_P|V], 
  new_rule(A,[A_P], R), % p :- p_P
  copy_term(A_P,A_P1),
  % add a fact for each possible rule for cautious reasoning (from EpP)
  gi_of_ep(EpP,GIofEpP),  
  %%%
  utl_rules_append(Af,[G,R,directive(minimize,{1,A_P1:A_P1}),directive(show,P_P/N)|GIofEpP], Af1),
  native_asp_enc(Af1,Ep0,En0,Ep,En,Ls, ASP).
native_asp_enc(Af,Ep0,En0,Ep,En,[_P/_N|Ls], ASP) :-
  % _P/_N is the predicate of a negative examples only
  native_asp_enc(Af,Ep0,En0,Ep,En,Ls, ASP).    

%
ep_choice([E],E).
ep_choice([E|Es],(E;Gs)) :-
  ep_choice(Es,Gs).

%
gi_of_cp(_CP1,_B1,[]) :-
  lopt(learning_mode(brave)).
gi_of_cp(CP1,B1,[G]) :-
  lopt(learning_mode(cautious)),
  new_rule(gi(CP1),B1, G).  

%
gi_of_ep(_EpP,[]) :-
  lopt(learning_mode(brave)). 
gi_of_ep([],[]) :-
  lopt(learning_mode(cautious)).
gi_of_ep([E|Ep],[G|Gs]) :-
  lopt(learning_mode(cautious)),
  new_rule(gi(E),[], G),
  gi_of_ep(Ep,Gs).


% ic(+Ep,+En, I), I is the list of integrity constratints
% generated from positive Ep and negative examples En
ic(Ep,En, I) :-
  lopt(learning_mode(brave)),
  !,
  ic_e(Ep,En, I).
ic(Ep,En, I) :-
  lopt(learning_mode(cautious)),
  !,
  ( En == [] -> 
    En1 = []
  ;
    findall((not E), member(E,En), En1)
  ),
  append(Ep,En1,Ec),
  ( Ec == [] -> 
    I = []
  ;
    I = [ic(Ec)]
  ).
  
  
%
ic_e([],[], []).
ic_e([],[N|Ns], [ic([N])|Rs]) :-
  ic_e([],Ns, Rs).
ic_e([P|Ps],Ns, [ic([not P])|Rs]) :-
  ic_e(Ps,Ns, Rs).
    

% MODE: list_to_conj(+Lst, -Conj)
% TYPE: list_to_conj(list(term), (term1,...,termN))
% SEMANTICS: generate the conjuntion (term1,...,termN)
% from the list of terms [term1,...,termN]

list_to_conj([H], H) :- !.
list_to_conj([H | T], ','(H, Conj)) :-
  list_to_conj(T, Conj).


%
asm_aux_rules(Ri, Rs) :-
  utl_rules(Ri, Us),
  findall(R, ( member(asm_cnt_dom(A,C,B),Us), copy_term((A,C,B),(A1,C1,B1)), new_rule(A1,[not C1|B1], R) ), Rs).

% -----------------------------------------------------------------------------
% ASP encoding of Ri by Lehtonen et al.
tjm_asp_enc(Ri,Ep0,En0,Ep,En,[], Ro) :-
  !,
  % encoding of rules
  aba_p_rules(Ri, PRs),
  tjm_aba_rules_enc(PRs, TJM_PRs),
  aba_p_rules(Ri1, TJM_PRs), 
  aba_ni_rules(Ri, NiRs),
  tjm_aba_rules_enc(NiRs, TJM_NiRs),
  aba_ni_rules(Ri1, TJM_NiRs),
  % encoding of assumptions  
  aba_asms(Ri, Asms),
  tjm_aba_asms_enc(Asms, TJM_Asms),
  aba_ni_rules_append(Ri1,TJM_Asms, Ri2),
  % encoding of contraries
  aba_cnts(Ri, Cnts),
  tjm_aba_cnts_enc(Cnts, TJM_Cnts),
  aba_ni_rules_append(Ri2,TJM_Cnts, Ri3),   
  % encoding of utility predicates   
  utl_rules(Ri, Us), 
  utl_rules(Ri3,Us),                                           
  % ic of the already covered examples
  tjm_ic(Ep0,En0, I1),
  % ic of the examples to be learnt
  tjm_ic(Ep,En, I2), 
  append(I1,I2,Ic),
  utl_rules_append(Ri3,Ic,Ro).
tjm_asp_enc(Af,Ep0,En0,Ep,En,[P/N|Ls], ASP) :-
  functor(C,P,N), % C is the atom with functor P/N
  aba_cnts(Af, Cs), % Cs: list of contraries in the ABA framework Af
  member(contrary(A,C),Cs), % C is a contrary (i.e., it belongs to Cs)
  !, % P/N is the predicate of a contrary
  %utl_rules(Af,Us), % U is the list of utility rules in Af
  %member(asm_cnt_dom(A,_,B),Us), % retrieve the domain B of the assumption A 
  %copy_term((C,B),(C1,B1)), % get a copy of the contrary C and its context B
  copy_term((A,C),(A1,C1)),
  C1 =.. [P|V], % get the variables of C1
  atom_concat(P,'_P',C_P), % primed version of the predicate P
  CP1 =.. [C_P|V], % primed version of the contrary
  new_rule({CP1},[contrary(A1,C1)], G), % {supported(p_P)} :- B
  new_rule(C1,[CP1], R), % p :- p_P
  tjm_aba_gen_rule_enc(R,Rg),
  copy_term(CP1,CP2),
  utl_rules_append(Af,[G,Rg,directive(minimize,{1,CP2:CP2}),directive(show,C_P/N)], Af1),
  tjm_asp_enc(Af1,Ep0,En0,Ep,En,Ls, ASP).
tjm_asp_enc(Af,Ep0,En0,Ep,En,[P/N|Ls], ASP) :-
  atom_concat(P,'_P',P_P), 
  findall(E1, ( member(E,Ep), functor(E,P,N), E =..[P|A], E1 =..[P_P|A] ), EpP), 
  EpP = [_|_], 
  !, % P/N is the predicate of at least one positive example
  ep_choice(EpP, EpG), 
  new_rule({EpG},[], G),
  length(V,N), A =.. [P|V], A_P =.. [P_P|V], 
  new_rule(A,[A_P], R), % p :- p_P
  tjm_aba_gen_rule_enc(R,Rg),
  copy_term(A_P,A_P1),
  utl_rules_append(Af,[G,Rg,directive(minimize,{1,A_P1:A_P1}),directive(show,P_P/N)], Af1),
  tjm_asp_enc(Af1,Ep0,En0,Ep,En,Ls, ASP).
tjm_asp_enc(Af,Ep0,En0,Ep,En,[_P/_N|Ls], ASP) :-
  % _P/_N is the predicate of a negative examples only
  tjm_asp_enc(Af,Ep0,En0,Ep,En,Ls, ASP).    

%
tjm_aba_rules_enc(Rs, TJM_Rs) :-
  tjm_aba_rules_enc(Rs,[], TJM_Rs).

%
tjm_aba_rules_enc([],Rs, Rs).
tjm_aba_rules_enc([R|Rs],Ns, Rs1) :-
  tjm_aba_rule_enc(R, E),
  append(Ns,E,Ns1),
  tjm_aba_rules_enc(Rs,Ns1, Rs1).

%
tjm_aba_rule_enc(R, [Henc|Benc]) :-
  copy_term(R,CpyR),
  rule_id(CpyR,I),
  rule_hd(CpyR,H),
  rule_bd(CpyR,B),
  unify_eqs(B,B1),
  tjm_aba_head(H,B1,I, ID,IDD,Henc), % head fact
  ( B1 == [] ->
    Benc = []
  ;
    tjm_aba_body(B1,ID,IDD, Benc) % body fact
  ).  

%
unify_eqs([],[]).
unify_eqs([V=C|E],R) :-
  V=C,
  !,
  unify_eqs(E,R).  
unify_eqs([B|E],[B|R]) :-
  unify_eqs(E,R).  

%
tjm_aba_head(H,B,I,  ID,D,Henc) :-
  term_variables_w_domains((H,B), V,D),
  ID =.. [id,I|V],
  T  =.. [head,ID,H],
  new_rule(T,D, Henc). % head fact

%
tjm_aba_body([],_,_, []).
tjm_aba_body([B|Bs],ID,D, [R|Rs]) :-
  T  =.. [body,ID,B],
  new_rule(T,D, R), % head fact  
  tjm_aba_body(Bs,ID,D, Rs).

%
term_variables_w_domains(T, V,D) :-
  term_variables(T, V),
  domains_of(V,D).

% 
domains_of([], []).
domains_of([T|Ts], [dom(T)|TwD]) :-
  domains_of(Ts, TwD).

% 
domains_of([],_,Flag, [],Flag).
domains_of([T|Ts],Vars,FlagI, TwD,FlagO) :-
  memberchk_eq(T,Vars),
  !,
  domains_of(Ts,Vars,FlagI, TwD,FlagO). 
domains_of([T|Ts],Vars,_FlagI, [dom(T)|TwD],FlagO) :-
  domains_of(Ts,Vars,yes, TwD,FlagO).  

%
tjm_aba_asms_enc([], []).
tjm_aba_asms_enc([A|As], [R|Rs]) :-
  term_variables(A, V),
  domains_of(V,D),
  new_rule(A,D,R),
  tjm_aba_asms_enc(As, Rs).

%
tjm_aba_cnts_enc([], []).
tjm_aba_cnts_enc([contrary(A,C)|Cs], [R|Rs]) :-
  new_rule(contrary(A,C),[assumption(A)],R),
  tjm_aba_cnts_enc(Cs, Rs). 

% tjm_ic(+Ep,+En, I), I is the list of integrity constratints
% generated from positive Ep and negative examples En
tjm_ic([],[], []).
tjm_ic([],[N|Ns], [ic([supported(N)])|Rs]) :-
  tjm_ic([],Ns, Rs).
tjm_ic([P|Ps],Ns, [ic([not supported(P)])|Rs]) :-
  tjm_ic(Ps,Ns, Rs).  

%
tjm_aba_gen_rule_enc(R, Rg) :-
  copy_term(R,CpyR),
  rule_id(CpyR,I),
  rule_hd(CpyR,H),
  rule_bd(CpyR,B),
  unify_eqs(B,B1),
  % encode head
  term_variables_w_domains(H, V,D),
  ID =.. [id,I|V],
  T  =.. [head,ID,H],
  append(D,B1,B2),
  new_rule(T,B2, Rg).