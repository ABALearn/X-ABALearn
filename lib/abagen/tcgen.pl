:- use_module(library(random)).
:- use_module(library(gensym)).

:- consult('../../xabal.pl').

% Pred: a nonempty list of length P of predicate symbols
% Asm: a nonempty list of assumptions not in Pred
% Contr: a list of pairs (assumption,contrary)

% generate_abaf(+P,+C,+A,+F,+BdL,+R,-Pred,-Univ,-Facts,-Rules,-Asm,-Contr): 
% generate a flat abaf consisting of
% P # unary predicates
% C # constants
% A # assumptions
% F # facts 
% BdL Max Body length
% R # rules
% output: 
% Pred (predicates), Univ (constants),
% Facts (facts), Rules (rules), Asm (assumptions), Contr (contraries)
% Facts=[(p(X), X=c),...]  p in Pred, c in Univ
% Rules=[(p1(X),[p2(X),...]),...] p1,p2 in Pred

generate_abaf(P,C,A,F,BdL,R, Pred,Univ,Facts,Rules,Asm,Contr) :- 
   generate_lang(P,C,A,Pred,Univ,Asm,Contr),
   generate_aba_facts(Pred,Univ,Facts,F),
   generate_aba_rules(Pred,Asm,BdL,Rules,R).
   
% generate language
generate_lang(P,C,A,Pred,Univ,Asm,Contr) :-
   gen_pred(P,Pred),
   gen_const(C,Univ),
   gen_asm(A,Asm),
   gen_contr(Asm,Pred,Contr).

gen_pred(0,[]). 
gen_pred(N,[P|Ps]) :-
   N>=1,
   N1 is N-1,
   gensym(p,P),
   gen_pred(N1,Ps).

gen_const(0,[]). 
gen_const(N,[C|Cs]) :-
   N>=1,
   N1 is N-1,
   gensym(c,C),
   gen_const(N1,Cs).
   
gen_asm(0,[]). 
gen_asm(N,[A|As]) :-
   N>=1,
   N1 is N-1,
   gensym(a,A),
   gen_asm(N1,As).

% Contr = [(a(X),ca(X)),...] with a in Asm and ca in Asm U Pred
gen_contr(Asm,Pred,Contr) :-
   append(Asm,Pred,Ps),
   g_contr(Asm,Ps,Contr).

g_contr([],_,[]).
g_contr([A|Asm],Ps,[(Atom,CAtom)|Contr]) :-
   Atom=..[A,X],
   random_member(P,Ps),
   CAtom=..[P,X],
   g_contr(Asm,Ps,Contr).

% generate facts: (p(X),X=c) where p in Pred, c in Univ
generate_aba_facts(_Pred,_Univ,[],0).
generate_aba_facts(Pred,Univ,[F|Facts],M) :- 
    M>=1,
    M1 is M-1,
    random_member(P,Pred),
    H=..[P,X],
    random_member(C,Univ),
    F=(H,[X=C]),
    generate_aba_facts(Pred,Univ,Facts,M1).

% generate rules
generate_aba_rules(_Pred,_Asm,_BdL,[],0).
generate_aba_rules(Pred,Asm,BdL,[R|Rules],K) :- 
   K>=1,
   K1 is K-1,
   generate_aba_rule(Pred,Asm,BdL,R),
   generate_aba_rules(Pred,Asm,BdL,Rules,K1).

% generate rule: (H,B) where H is p(X) and B list of atoms [p1(X),...,pL(X)], with p,p1,...,pL (L>=1) in Pred, X variable
generate_aba_rule(Pred,Asm,BdL,(H,B)) :- 
    generate_hd(Pred,H,X),
    generate_bd(Pred,Asm,BdL,B,X).

generate_hd(Pred,H,X) :-
    random_member(P,Pred),
    H=..[P,X].

generate_bd(Pred,Asm,BdL,B,X) :-
    random_between(1,BdL,L),
    append(Pred,Asm,Ps),
    gen_bd(Ps,B,X,L).
    
gen_bd(_Ps,[],_X,0).
gen_bd(Ps,[A|B],X,L) :- 
    L>=1,
    L1 is L-1,
    random_select(P,Ps,Rest),
    A=..[P,X],
    gen_bd(Rest,B,X,L1).    

% print ABAF
print_abaf(Facts,Rules,Contr) :-
    print_rules(Facts),
    print_rules(Rules),
    print_contr(Contr).

print_rules([]).
print_rules([R|RR]) :- 
    print_rule(R), nl,
    print_rules(RR).
    
print_rule((H,B)) :-
    write(H), write(' :- '), print_bd(B).

print_bd([A]) :- 
    !,
    write(A), write('.').
print_bd([A1,A2|B]) :-
    write(A1), write(', '),
    print_bd([A2|B]).
    
print_contr([]).
print_contr([(At,CAt)|Cs]) :-
    write(assumption(At)), write('.'), nl,
    write(contrary(At,CAt) :- assumption(At) ), write('.'), nl,
    print_contr(Cs).

% print Examples (Pos e Neg)
print_ex(Pex,Nex) :-
    nl, 
    write('% '), write(pos_ex(Pex)), write('.'), nl,
    write('% '), write(neg_ex(Nex)), write('.'), nl.

% print X-ABALearn goal
print_goal(BaseFileName,Pex,Nex) :-
    atom_concat(BaseFileName,'.pl',FileName),
    tell(FileName),     
    write(':- xabal(\''), write(BaseFileName), write('\','), write(Pex), write(','), write(Nex), write(').'),
    told.

% generate examples:
% Ep #positive examples
% En #negative examples
% L #learnable predicates
% Pred: set of predicates in the language
% Facts: facts in the ABAF 
% Pex: positive examples
% Nex: negative examples

% Examples are generated from constants in Facts, learnable predicates may occur in BK
generate_ex(Ep,En,L,Pred,Facts,Pex,Nex) :-    
    rnd_learnable(L,Pred,T),             % rnd select learnable predicates in Pred
    constants_in(Facts,Const),           % compute constants occurring in Facts
    sort(Const,Univ),                    % avoid duplicates
    candidate_ex(T,Univ,Cex),            % candidate examples have predicate in T and argument a constant occurring in Facts
    rnd_select_ex(Ep,Cex,Pex,Rest),      % rnd select pos. ex.
    not_in_facts(Rest,Facts,CNex),       % exclude candidate examples appearing as facts in BK
    rnd_select_ex(En,CNex,Nex,_).        % rnd select neg. ex.
%
generate_ex(E,L,Pred,Facts,Ex) :-
    rnd_learnable(L,Pred,T),             % rnd select learnable predicates in Pred
    constants_in(Facts,Const),           % compute constants occurring in Facts
    sort(Const,Univ),                    % avoid duplicates
    candidate_ex(T,Univ,Cex),
    rnd_select_ex(E,Cex,Ex,_Rest).

%
arclaims_from_extensions_file(M,ABAFPREDBaseFileName,Pred,Cs,NPred,Exsize, S,LearnPred,SEp,SEn) :-
    read_bk(ABAFPREDBaseFileName, In),
    rules_aba_utl(In, ABAF),
    % generates only facts for predicates (no assumptions)
    findall(F/1,member(F,Pred),PredwArity),
    !,
    arclaims_from_extensions(M,ABAF,Cs,PredwArity, S,PEp,PEn),
    %%% select examples
    random_between(30,60, P),
    PosSize is round(Exsize * P/100),
    NegSize is Exsize - PosSize,
    generate_ex_from_claims(PEp,PEn,NPred,PosSize,NegSize, LearnPred,Ep,En),
    rnd_select_lst(PosSize,Ep, SEp),
    rnd_select_lst(NegSize,En, SEn).   

% arclaims_from_extensions/7
arclaims_from_extensions(x,ABAF,Cs,PredwArity, S,Ep,En) :-
    extension(ABAF,PredwArity, S),
    group_by_functor(S, Groups),
    arclaims_from_extension_aux(Groups,Cs, Ep,En).
arclaims_from_extensions(a,ABAF,Cs,PredwArity, C,Ep,En) :-
    abaf_consequences(ABAF,PredwArity, C,B),
    group_by_functor(C, Groups),
    arclaims_from_extensions_aux(Groups,B,Cs, Ep,En).
  
% S is a list
arclaims_from_extension_aux([],_Cs, [],[]).
arclaims_from_extension_aux([P/N-Ac|Gs],Cs, [(P/N,Ac,AcL)|Acs],[(P/N,Rj,RjL)|Rjs]) :-
    length(Ac,AcL),
    rejcl(P,Ac,Cs, Rj),
    length(Rj,RjL),
    arclaims_from_extension_aux(Gs,Cs, Acs,Rjs).
% S is a list of list
arclaims_from_extensions_aux([],_B,_Cs, [],[]).
arclaims_from_extensions_aux([P/N-Ac|Gs],B,Cs, [(P/N,Ac,AcL)|Acs],[(P/N,Rj,RjL)|Rjs]) :-
    length(Ac,AcL),
    rejcl(P,B,Cs, Rj),
    length(Rj,RjL), 
    arclaims_from_extensions_aux(Gs,B,Cs, Acs,Rjs).    

% group_by_functor(+Fs, -Groups)
% Groups is a list of (P/N)-Facts pairs, one per predicate occurring in Fs
group_by_functor(Fs, Groups) :-
    map_list_to_pairs(functor_key,Fs,Ps),
    keysort(Ps, Sorted),
    group_pairs_by_key(Sorted, Groups).

% functor_key(+F, -P/N)
% P/N is the predicate indicator of the term F
% (P its name, N its arity), used as a key for grouping.
functor_key(F, P/N) :-
    functor(F,P,N).

% Rj is a list of atoms of the form P(C), where C is a
% constant in Cs that does not occur as the argument of
% an atom in S.
rejcl(P,S,Cs, Rj) :-
    maplist(arg(1),S,As),
    sort(As, TBD),
    sort(Cs, All),
    ord_subtract(All,TBD, Cs1),
    maplist(make_atom(P),Cs1,Rj).

% make_atom(+P,+C, -A)
% A is the atom P(C)
make_atom(P,C, A) :-
    A =.. [P,C].

%
generate_ex_from_claims(Acc,Rej,NPred,PosSize,NegSize, Ps,FLs1,FLs2) :-
    rnd_select_k(Acc,NPred,PosSize, Ps,Ls1),
    select_cs(Rej,Ps, Ls2,S2),
    S2 >= NegSize,
    flatten(Ls1,FLs1),
    flatten(Ls2,FLs2).


% rnd_select_k(+Ts,+K,+M, -Ps,-Ls)
% Ts is a list of triples (P,L,N), where N is the length of L.
% Ps and Ls are the P and the L of K triples selected from Ts,
% such that the sum of the selected N is at least M.
% On backtracking, all such selections are enumerated in random order;
% fails if no (further) selection exists.
rnd_select_k(Ts,K,M, Ps,Ls) :-
    random_permutation(Ts, Perm),
    select_k(K,Perm,M, Ps,Ls).

% select_k(+K,+Ts,+M, -Ps,-Ls)
% Ps and Ls are the P and the L of K triples taken from Ts (in order)
% whose N sum to at least M
% (enumerated on backtracking, by chronological backtracking)
select_k(0,_,M, [],[]) :-
    !,
    M =< 0.
select_k(K,[(P,L,N)|Ts],M, [P|Ps],[L|Ls]) :-
    K1 is K-1,
    M1 is M-N,
    select_k(K1,Ts,M1, Ps,Ls).
select_k(K,[_|Ts],M, Ps,Ls) :-
    select_k(K,Ts,M, Ps,Ls).

% select_cs(+Ts,+Cs, -Ls,-S)
% Ts is a list of triples (P,L,N); Cs is a list of constants.
% Ls are the L of the triples in Ts whose P occurs in Cs
% (in the order of Ts); S is the sum of the corresponding N.
select_cs(Ts,Cs, Ls,S) :-
    select_cs(Ts,Cs,0, Ls,S).

select_cs(_,[],S, [],S).
select_cs(Ts,[P|Cs],S0, [L|Ls],S) :-
    select((P,L,N),Ts,Rs),
    !,
    S1 is S0+N,
    select_cs(Rs,Cs,S1, Ls,S).   
    
%
abaf_consequences(ABAF,Ps, C,B) :-
  % for each P/N in Ps, add a show directive
  % if Ps is empty, then the extension includes all the predicates 
  findall(directive(show,P/N),member(P/N,Ps),Sw),
  utl_rules_append(ABAF,Sw,Rs),
  % create the ASP encoding
  asp(Rs,[],[],[],[],[], RsASP),
  % write rules to file
  dump_rules(RsASP),
  % invoke clingo to compute the answer sets of RsASP and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | awk \'/Answer:/ {f=NR}; f && NR==f+1 { last = $0 } END { print "[" last "]." }\' > cc.pl'),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'',EXIT_CODE),
  !,
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  see('cc.pl'),
  % read 'cc.clingo' - read first extension
  read_all([C]),
  seen,
  % invoke clingo to compute the answer sets of RsASP and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --enum-mode=brave > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | awk \'/Answer:/ {f=NR}; f && NR==f+1 { last = $0 } END { print "[" last "]." }\' > cc.pl'), 
  see('cc.pl'),
  % read 'cc.clingo' - read first extension
  read_all([B]),
  seen.  
% assert all terms from file
read_all([A|As]) :-
  read(A),
  A \== end_of_file,
  !,
  read_all(As).
read_all([]).

rnd_learnable(0,_Pred,[]). 
rnd_learnable(L,Pred,[P|T]) :- 
    L>=1,
    L1 is L-1,
    random_select(P,Pred,Pred1),
    rnd_learnable(L1,Pred1,T).

n_random_select(0,_Pred,[]). 
n_random_select(L,Pred,[P|T]) :- 
    L>=1,
    L1 is L-1,
    random_select(P,Pred,Pred1),
    n_random_select(L1,Pred1,T).
%
n_random_select(0,Pred,[],Pred). 
n_random_select(L,Pred,[P|T],Rest) :- 
    L>=1,
    L1 is L-1,
    random_select(P,Pred,Pred1),
    n_random_select(L1,Pred1,T,Rest).

%
constants_in([],[]).
constants_in([(_H,B)|Rules],U) :- 
    findall(C,member(_=C,B),Cs),
    append(Cs,U1,U),
    constants_in(Rules,U1).

% Candidate examples
candidate_ex(T,Univ,Cex) :- 
    findall(Ex,(member(P,T), member(C,Univ), Ex=..[P,C]), Cex).

rnd_select_ex(0,Cex,[],Cex).
rnd_select_ex(N,Cex,Ex,Rest) :-
    N>=1,
    N1 is N-1,
    Cex=[_|_],
    random_select(E,Cex,Cex1),
    Ex=[E|Ex1],
    rnd_select_ex(N1,Cex1,Ex1,Rest).
    
%
not_in_facts([],_Facts,[]).
not_in_facts([Ex|Exs],Facts,[Ex|CNex]) :- 
    Ex=..[P,C],
    H=..[P,X],
    F=(H,[X=C]),
    \+ member(F,Facts), !,
    not_in_facts(Exs,Facts,CNex).
not_in_facts([_Ex|Exs],Facts,CNex) :- 
    not_in_facts(Exs,Facts,CNex).

%
rnd_select_lst(0,_,[]) :-
    !.
rnd_select_lst(N,L,[E|Ex]) :-
    N>=1,
    !,
    N1 is N-1,
    random_select(E,L,L1),
    rnd_select_lst(N1,L1,Ex).

%
rnd_select_lst(0,R,[],R) :-
    !.
rnd_select_lst(N,L,[E|Ex],R) :-
    N>=1,
    !,
    N1 is N-1,
    random_select(E,L,L1),
    rnd_select_lst(N1,L1,Ex,R).

% rnd_delete_lst(+N,+Rs, -SRs)
% SRs is obtained from Rs by randomly removing N elements.
% Fails if Rs has fewer than N elements.
rnd_delete_lst(0,Rs, Rs) :-
    !.
rnd_delete_lst(N,Rs, SRs) :-
    N1 is N-1,
    random_select(_,Rs,Rs1),
    rnd_delete_lst(N1,Rs1, SRs).

% rem_hdpred_rules(+Rs, +ExPred, -RsO)
% RsO is obtained from Rs by removing every rule whose head predicate
% occurs in ExPred.
rem_hdpred_rules([],_,[]).
rem_hdpred_rules([R|Rs],ExPred,Rs1) :-
    R=(H,_),
    pred_in([H],ExPred), 
    !,
    rem_hdpred_rules(Rs,ExPred,Rs1).
rem_hdpred_rules([R|Rs],ExPred,[R|Rs1]) :-
    rem_hdpred_rules(Rs,ExPred,Rs1).
        

% rem_pred_rules(+Rs, +ExPred, -RsO)
% RsO is obtained from Rs by removing every rule whose head predicate
% occurs in ExPred and every rule whose body contains at least one
% atom whose predicate occurs in ExPred.
rem_pred_rules([],_,[]).
rem_pred_rules([R|Rs],ExPred,Rs1) :-
    R=(H,B),
    pred_in([H|B],ExPred), 
    !,
    rem_pred_rules(Rs,ExPred,Rs1).
rem_pred_rules([R|Rs],ExPred,[R|Rs1]) :-
    rem_pred_rules(Rs,ExPred,Rs1).

%
pred_in([E|_],ExPred) :-
    functor(E,F,1),
    member(F/1,ExPred),
    !.
pred_in([_|Es],ExPred) :-
    pred_in(Es,ExPred).


% generate_abalpb(P,C,A,F,R,Ep,En,L,Facts,Rules,Asm,Contr,Pex,Nex)
% P # unary predicates
% C # constants
% A # assumptions
% F # facts  
% BdL Max Body length
% R # rules
% Ep # positive examples
% En # negative examples
% L # learnable predicates
% output: Facts (facts), Rules (rules), Asm (assumptions), Contr (contraries),
% Pex (positive examples), Nex (negative examples)

generate_abalpb(P,C,A,F,BdL,R,Ep,En,L,Facts,Rules,Asm,Contr,Pex,Nex) :-
    generate_abaf(P,C,A,F,BdL,R,Pred,_Univ,Facts,Rules,Asm,Contr),
    generate_ex(Ep,En,L,Pred,Facts,Pex,Nex).


% Examples are generated from constants in Facts, learnable predicates do not occur in BK
generate_disjoint_ex(Ep,En,L,T,Facts,Pex,Nex) :-    
    gen_disjoint_pred(L,T),
    constants_in(Facts,Const),
    sort(Const,Univ),
    candidate_ex(T,Univ,Cex),        
    rnd_select_ex(Ep,Cex,Pex,Rest),
    rnd_select_ex(En,Rest,Nex,_).

gen_disjoint_pred(0,[]). 
gen_disjoint_pred(N,[P|Ps]) :-
   N>=1,
   N1 is N-1,
   gensym(t,P),
   gen_disjoint_pred(N1,Ps).

% Fixing some parameters:
% general ABAF learning problem
export_abalpb(BKsize,Ep,En) :-
    R is div(BKsize,3),
    hparams(BKsize,R, P,C,A,F,BdL,L),
    generate_abaf(P,C,A,F,BdL,R,Pred,_Univ,Facts,Rules,_Asm,Contr),
    generate_ex(Ep,En,L,Pred,Facts,Pex,Nex),
    %%%
    abalp_filename('abalpb.bk.',BaseFileName,ABAFFileName),
    tell(ABAFFileName),
    print_abaf(Facts,Rules,Contr),
    print_ex(Pex,Nex),
    told,
    print_goal(BaseFileName,Pex,Nex),
    write('ABA Learning problem written on file '), write(ABAFFileName), nl.
export_abalpb(BKsize,E) :-
    random_ex_size(E,Ep,En),
    export_abalpb(BKsize,Ep,En).    
% learnable predicates do not occur in the BK
export_disjoint_abalpb(BKsize,Ep,En) :-
    R is div(BKsize,3), 
    hparams(BKsize,R, P,C,A,F,BdL,L),
    % generate ABA Learning problems where learnable predicates do not occur in ABAF 
    generate_abaf(P,C,A,F,BdL,R,_Pred,_Univ,Facts,Rules,_Asm,Contr),
    generate_disjoint_ex(Ep,En,L,_T,Facts,Pex,Nex),
    %%%
    abalp_filename('dis_abalpb.bk.',BaseFileName,ABAFFileName),
    tell(ABAFFileName),
    print_abaf(Facts,Rules,Contr),
    print_ex(Pex,Nex),
    told,
    print_goal(BaseFileName,Pex,Nex),
    write('ABA Learning problem written on file '), write(ABAFFileName), nl.    
export_disjoint_abalpb(BKsize,E) :-
    random_ex_size(E,Ep,En),
    export_disjoint_abalpb(BKsize,Ep,En).   
% BK is a set of facts
export_tabular_abalpb(BKsize,Ep,En) :-
    R = 0,  
    hparams(BKsize,R, P,C,_A,F,_BdL,L),
    generate_abaf(P,C,0,F,0,0,_Pred,_Univ,Facts,Rules,_Asm,Contr),
    generate_disjoint_ex(Ep,En,L,_T,Facts,Pex,Nex),
    %%%
    abalp_filename('tab_abalpb.bk.',BaseFileName,ABAFFileName),
    tell(ABAFFileName),
    print_abaf(Facts,Rules,Contr),
    print_ex(Pex,Nex),
    told,
    print_goal(BaseFileName,Pex,Nex),
    write('ABA Learning problem written on file '), write(ABAFFileName), nl.  
export_tabular_abalpb(BKsize,E) :-
    random_ex_size(E,Ep,En),
    export_tabular_abalpb(BKsize,Ep,En).    
%
hparams(BKsize,R, P,C,A,F,BdL,L) :-
    BKsize >= 4,
    !,
    F is BKsize-R,
    P is div(BKsize,4),
    C is div(BKsize,2),
    A is div(P,3)+1,
    BdL=2,
    L=1.

%
random_ex_size(E,Ep,En) :-
    E>=2,
    E1 is E-1,
    random_between(1,E1,Ep),
    En is E - Ep.

abalp_filename(BaseFileNameIn, BaseFileNameOut,ABAFFileName) :-
    gensym(BaseFileNameIn,BaseFileNameOut),
    atom_concat(BaseFileNameOut,'.aba',ABAFFileName).

% :-  export_abalpb(10,2,3).
% :-  export_disjoint_abalpb(10,2,2).
% :-  export_tabular_abalpb(10,3,1).

try(Max,G) :-
  try_aux(1,Max,G).
try_aux(N,Max,_) :-
  N >= Max, !.
try_aux(N,Max,G) :-
  N =< Max,
  ( G -> true ; ( M is N+1, try_aux(M,Max,G) ) ).

% export_abalpb/4
export_abalpb(Mode,Type,BKsize,Exsize) :-
    ( BKsize>=10, Exsize>=5 ),
    oracle_hparams(BKsize, R,P,C,A,F,BdL),
    gensym('abaf.',BaseFileName),
    generate_abaf(P,C,A,F,BdL,R, Pred,Univ,Facts,Rules,Asms,Contr),
    %%%
    oracle_filename(BaseFileName,ORACLEFileName),
    tell(ORACLEFileName),
    print_abaf(Facts,Rules,Contr),
    told,
    % LearnPred is a subset of the predicates different from assumptions
    ( Type == tabular 
    ->  NPred = 1
    ;   (  length(Pred,NPred),
           random_between(1,NPred,TBL),
           NPred = TBL % TBL1 is min(30,TBL),    
        )
    ),
    % Examples are generated from extensions
    constants_in(Facts, Cs),
    ( arclaims_from_extensions_file(Mode,ORACLEFileName,Pred,Cs,NPred,Exsize, S,LearnPred,Ep,En) -> 
      true 
    ; 
      ( delete_file(ORACLEFileName), fail ) 
    ),
    write('oracle: '), write(ORACLEFileName), nl,
    write('  BK size: '), write(BKsize), nl, 
    write('  Facts:   '), length(Facts,FactsL), write(FactsL), nl,
    write('  Rules:   '), length(Rules,RulesL), write(RulesL), nl,   
    write('  Pred.:   '), length(Pred,PredL), write(PredL), nl,
    write('  Univ.:   '), length(Univ,UnivL), write(UnivL), nl,
    write('  Asms.:   '), length(Asms,AsmsL), write(AsmsL), nl,
    write('  Cont.:   '), length(Contr,ContrL), write(ContrL), nl,
    write('  Learn.:  '), write(NPred), write(' '), write(LearnPred), nl,          
    %%% generate an ABAF learning problem of type Type  
    export_abalpb(Type,BaseFileName,S,Facts,Rules,Contr,LearnPred, ABALPBFileName,SFacts,SRules),
    !,
    %%% 5fCV
    random_five_fold(Ep, EpRP),
    random_five_fold(En, EnRP),
    atom_concat(BaseFileName,'.5fCV.pl',FileName),
    tell(FileName),
    write(':- dynamic bk/1, lp/1, fold/5.'), nl,
    writebkfile(ABALPBFileName),
    write('lp('), write(LearnPred), write(').'), nl,
    write_5fcv(1,EpRP,EnRP),
    told,
    %%%
    write('abalpb: '), nl,
    write('  Mode: '), write(Mode), nl,
    write('  Facts:   '), length(SFacts,SFactsL), write(SFactsL), nl,
    write('  Rules:   '), length(SRules,SRulesL), write(SRulesL), nl,       
    write('  Pos.Ex.: '), length(Ep,EpL), write(EpL), nl,
    write('  Neg.Ex.: '), length(En,EnL), write(EnL), nl,    
    %%%
    %term_to_atom(LearnPred,NormLearnPredAtom),
    %term_string(FileName,FileNameS),    
    append_csv_data('tcgen.csv', 
        [row(ORACLEFileName,BKsize,FactsL,RulesL,PredL,UnivL,AsmsL,ContrL,Exsize,NPred,Mode,
             ABALPBFileName,SFactsL,SRulesL,EpL,EnL)]
    ).   

%
oracle_hparams(BKsize, R,P,C,A,F,BdL) :-
    R is max(1,div(BKsize,4)),
    F is BKsize-R,
    P is 10 + div(BKsize,20),
    C is div(BKsize,3),
    A is 1 + div(P,3),
    BdL=2.    

writebkfile(File) :-
    exists_file(File),
    !,
    write('bk('), writeq(File), write(').'), nl.
writebkfile(_File).

deletefile(File) :-
    exists_file(File),
    !,
    delete_file(File).
deletefile(_File).

%
oracle_filename(BaseFileName,ORACLEFileName) :-
    atom_concat(BaseFileName,'.oracle.aba',ORACLEFileName).
%
genlp_filename(BaseFileName,GENLPFileName) :-
    atom_concat(BaseFileName,'.genlp.aba',GENLPFileName).
%
dislp_filename(BaseFileName,DISLPFileName) :-
    atom_concat(BaseFileName,'.dislp.aba',DISLPFileName).
%
cnslp_filename(BaseFileName,DISLPFileName) :-
    atom_concat(BaseFileName,'.cnslp.aba',DISLPFileName).    
%
tablp_filename(BaseFileName,TABLPFileName) :-
    atom_concat(BaseFileName,'.tablp.aba',TABLPFileName).  

%%%
% generate constrained learning problem
export_abalpb(Type,BaseFileName,_S,Facts,Rules,Contr,LearnPred, CNSLPFileName,Facts,SRules) :-
    Type = constrained,
    !,
    cnslp_filename(BaseFileName,CNSLPFileName),
    rem_hdpred_rules(Rules,LearnPred,SRules),
    tell(CNSLPFileName),
    print_abaf(Facts,SRules,Contr),
    told,
    read_abaf(CNSLPFileName, CNSLPABAF),
    ( satisfiable(CNSLPABAF) -> 
      true
    ;
      ( oracle_filename(BaseFileName,ORACLEFileName),
        delete_file(ORACLEFileName), 
        delete_file(CNSLPFileName), 
        fail 
      )
    ).

%%%
% generate disjont learning problem
export_abalpb(Type,BaseFileName,_S,Facts,Rules,Contr,LearnPred, DISLPFileName,Facts,SRules) :-
    Type = disjoint,
    !,
    dislp_filename(BaseFileName,DISLPFileName),
    rem_pred_rules(Rules,LearnPred,SRules),
    tell(DISLPFileName),
    print_abaf(Facts,SRules,Contr),
    told,
    read_abaf(DISLPFileName, DISLPABAF),
    ( satisfiable(DISLPABAF) -> 
      true
    ;
      ( oracle_filename(BaseFileName,ORACLEFileName),
        delete_file(ORACLEFileName), 
        delete_file(DISLPFileName), 
        fail 
      )
    ).

%%%
% generate and export a general learning problem
export_abalpb(Type,BaseFileName,_S,Facts,Rules,Contr,_LearnPred, GENLPFileName,Facts,SRules) :-
    Type = general,
    !,
    genlp_filename(BaseFileName,GENLPFileName),
    length(Rules,RulesLength),
    random_between(20,50, P),
    TBD is round(RulesLength * P/100),
    rnd_delete_lst(TBD,Rules, SRules),
    tell(GENLPFileName),
    print_abaf(Facts,SRules,Contr),
    told,
    read_abaf(GENLPFileName, GENLPABAF), 
    ( satisfiable(GENLPABAF) ->
      true
    ;
      ( oracle_filename(BaseFileName,ORACLEFileName),
        delete_file(ORACLEFileName), 
        delete_file(GENLPFileName), 
        fail 
      )
    ).

%%%
% generate tabular learning problem
export_abalpb(Type,BaseFileName,S,_Facts,_Rules,_Contr,LearnPred, TABLPFileName,SFacts,[]) :-
    Type = tabular,
    !,
    tablp_filename(BaseFileName,TABLPFileName),    
    atoms2facts(S,Facts),
    rem_pred_rules(Facts,[dom/1|LearnPred], SFacts),
    tell(TABLPFileName),    
    print_abaf(SFacts,[],[]),
    told.

atoms2facts([],[]).
atoms2facts([A|As],[R|Rs]) :-
    A =..[P|Args],
    args2Eqs(Args, Eqs,Vs),
    H =..[P|Vs],
    R = (H,Eqs),
    atoms2facts(As,Rs).
%
args2Eqs([], [],[]).
args2Eqs([A|As], [A=V|Eqs],[V|Vs]) :-
    args2Eqs(As, Eqs,Vs).

%
read_abaf(FileName, ABAF) :-
    read_bk(FileName, In),
    rules_aba_utl(In, ABAF).

%
random_five_fold(S, RP) :- 
  random_five_fold(S,[[],[],[],[],[]], RP).
%
random_five_fold([],RP, RP) :- 
  !.
random_five_fold(S,[S1,S2,S3,S4,S5], RP) :-
  random_select(E,S, R),
  random_five_fold(R,[S2,S3,S4,S5,[E|S1]], RP).

%
write_5fcv(6,_,_).
write_5fcv(I,EpRP,EnRP) :-
    nth1(I,EpRP,SEp,REp), flatten(REp,FREp), 
    nth1(I,EnRP,SEn,REn), flatten(REn,FREn),
    write(fold(I,FREp,FREn,SEp,SEn)), write('.'), nl,
    I1 is I+1,
    write_5fcv(I1,EpRP,EnRP).


append_csv_data(File, Rows) :-
    % Check if the file does not exist or is empty (size 0)
    ( ( \+ exists_file(File) ; size_file(File, 0) ) ->
        NeedsHeader = true
    ;   
        NeedsHeader = false
    ),
    setup_call_cleanup(
        open(File, append, Out),
        (( NeedsHeader == true ->
          % write header row
          csv_write_stream(Out, [row('Oracle','#BK','#Facts','#Rules','#Preds','#Asms','#Const','#Ex','#Learn','Mode',
                                     'ABAFLP','#Facts','#Rules','#Ep','#En')], [])
          ;   
            true
        ), 
        % write data row
        csv_write_stream(Out, Rows, []) 
        ),
        close(Out)
    ).

% generate a test cases of size BKsize with E examples each for mode M
tcgen(Mode,Type,BKsize,Exsize) :-
  try(50,export_abalpb(Mode,Type,BKsize,Exsize)),
  !.
tcgen(Mode,Type,BKsize,Exsize) :-
  write('WARNING: '), write(tcgen(Mode,Type,BKsize,Exsize)), write('failed 50 times!'), nl.

% generate N test cases
tcgen(0,_Mode,_Type,_BKsize,_Exsize).
tcgen(N,Mode,Type,BKsize,Exsize) :-
  N>=1,
  N1 is N-1,
  tcgen(Mode,Type,BKsize,Exsize),
  tcgen(N1,Mode,Type,BKsize,Exsize).
