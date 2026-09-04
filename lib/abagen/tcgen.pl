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

generate_abaf(P,C,A,F,BdL,R,Pred,Univ,Facts,Rules,Asm,Contr) :- 
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

print_bd([A]) :- write(A), write('.').
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

arclaims_from_extensions(M,ABAFPREDBaseFileName,PredwArity,Univ,E, Ep,SEp,En,SEn) :-
    read_bk(ABAFPREDBaseFileName, In),
    rules_aba_utl(In, ABAF),
    !,
    arclaims_from_extensions(M,ABAF,PredwArity,Univ, PEp,PEn),
    generate_ex_from_claims(PEp,PEn,PredwArity, Ep,En),
    H is div(E,2),
    n_random_select(H,Ep,SEp),
    n_random_select(H,En,SEn).

%
arclaims_from_extensions(x,ABAF,PredwArity,Univ, Ep,En) :-
    extension(ABAF,PredwArity, S),
    arclaims_from_extension_aux(S,PredwArity,Univ, Ep,En).
arclaims_from_extensions(a,ABAF,PredwArity,Univ, Ep,En) :-
    extensions(ABAF,PredwArity, S),
    arclaims_from_extensions_aux(S,PredwArity,Univ, Ep,En).
    
% S is a list
arclaims_from_extension_aux(_S,[],_Univ, [],[]).
arclaims_from_extension_aux(S,[P/N|Preds],Univ, [(P/N,Ep)|Eps],[(P/N,En)|Ens]) :-
    findall(Pos,(member(Pos,S),functor(Pos,P,N)),Ep),
    findall(Neg,(member(C,Univ),Neg=..[P,C],\+member(Neg,Ep)),En),
    arclaims_from_extension_aux(S,Preds,Univ, Eps,Ens).
% S is a list of list
arclaims_from_extensions_aux(_S,[],_Univ, [],[]).
arclaims_from_extensions_aux(S,[P/N|Preds],Univ, [(P/N,Ep)|Eps],[(P/N,En)|Ens]) :-
    findall(Pos,(functor(Pos,P,N),maplist(member(Pos),S)),Ep),
    findall(Neg,(member(C,Univ),Neg=..[P,C],maplist(nonmember(Neg),S)),En),
    arclaims_from_extensions_aux(S,Preds,Univ, Eps,Ens).    

nonmember(E,L) :-
    memberchk(E,L), % assuming E ground
    !,
    fail.
nonmember(_,_).

generate_ex_from_claims(Acc,Rej,Preds, FEp,FEn) :-
    findall(Ep,(member(P,Preds),member((P,Ep),Acc)),EpL), flatten(EpL,FEp), FEp \= [],
    findall(En,(member(P,Preds),member((P,En),Rej)),EnL), flatten(EnL,FEn), FEn \= [].


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


    
constants_in([],[]).
constants_in([(_H,B)|Rules],U) :- 
    findall(C,member(_=C,B),Cs),
    append(Cs,U1,U),
    constants_in(Rules,U1).

% Candidate examples
candidate_ex(T,Univ,Cex) :- 
    findall(Ex,(member(P,T), member(C,Univ), Ex=..[P,C]), Cex).

rnd_select_ex(0,Cex,[],Cex).
%rnd_select_ex(N,[],[],[]) :- N>=1.
rnd_select_ex(N,Cex,Ex,Rest) :-
    N>=1,
    N1 is N-1,
    Cex=[_|_],
    random_select(E,Cex,Cex1),
    Ex=[E|Ex1],
    rnd_select_ex(N1,Cex1,Ex1,Rest).

not_in_facts([],_Facts,[]).
not_in_facts([Ex|Exs],Facts,[Ex|CNex]) :- 
    Ex=..[P,C],
    H=..[P,X],
    F=(H,[X=C]),
    \+ member(F,Facts), !,
    not_in_facts(Exs,Facts,CNex).
not_in_facts([_Ex|Exs],Facts,CNex) :- 
    not_in_facts(Exs,Facts,CNex).

rnd_select_lst(0,_,Rest,Rest).
rnd_select_lst(N,L,[E|Ex],Rest) :-
    N>=1,
    N1 is N-1,
    random_select(E,L,L1),
    rnd_select_lst(N1,L1,Ex,Rest).

rem_pred_rules([],_,[]).
rem_pred_rules([R|Rs],ExPred,Rs1) :-
    R=(H,_),
    functor(H,F,1),
    member(F/1,ExPred), 
    !,
    rem_pred_rules(Rs,ExPred,Rs1).
rem_pred_rules([R|Rs],ExPred,[R|Rs1]) :-
    rem_pred_rules(Rs,ExPred,Rs1).

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


export_predictor_abalpb(M,BKsize,E) :-
    ( BKsize>=3, E>=10 ),
    R is div(BKsize,3),
    hparams(BKsize,R, P,C,A,F,BdL,_L), % L = learnable predicates
    gensym('abaf.',BaseFileName),
    generate_abaf(P,C,A,F,BdL,R,Pred,Univ,Facts,Rules,_Asm,Contr),
    %%%
    atom_concat(BaseFileName,'.pred.aba',ABAFPREDFileName),
    tell(ABAFPREDFileName),
    print_abaf(Facts,Rules,Contr),
    told,
    write('ABA Learning problem written on file '), write(ABAFPREDFileName), nl,
    %%%
    select_learnable_pred(Rules,LearnPred),
    % Examples are generated from extensions
    % Hence, constants occurring in examples occur in facts as well
    % LearnPred is a subset of the predicates of Rules
    ( arclaims_from_extensions(M,ABAFPREDFileName,LearnPred,Univ,E, Ep,SEp,En,SEn) -> 
      true 
    ; 
      ( delete_file(ABAFPREDFileName), fail ) 
    ),
    !,
    delete_file(ABAFPREDFileName),
    write('predictor: '), nl,
    write('  BK size: '), write(BKsize), nl, 
    write('  Rules:   '), length(Rules,RulesL), write(RulesL), nl,
    write('  Facts:   '), length(Facts,FactsL), write(FactsL), nl,
    write('  Pred.:   '), length(Pred,PredL), write(PredL), nl,
    write('  Univ.:   '), length(Univ,UnivL), write(UnivL), nl,    
    write('  Learn.:  '), length(LearnPred,LearnPredL), write(LearnPredL), write(' '), write(LearnPred), nl,
    write('  Pos.Ex. (Tot.Pos.): '), length(SEp,SEpL), write(SEpL), length(Ep,EpL), write(' ('), write(EpL), write(')'), nl,
    write('  Neg.Ex. (Tot.Neg.): '), length(SEn,SEnL), write(SEnL), length(En,EnL), write(' ('), write(EnL), write(')'), nl,    
    %%% ABALPB - remove half of the rules
    length(Rules,RulesLength),
    H is div(RulesLength,2),
    rnd_select_lst(H,Rules,SRules,_),
    atom_concat(BaseFileName,'.genlp.aba',GENLPFileName),
    tell(GENLPFileName),
    print_abaf(Facts,SRules,Contr),
    told,
    write('general ABALP: '), nl,
    write('  Rules:   '), length(SRules,SRulesL), write(SRulesL), nl, 
    %%% DIS_ABALPB - remove all rules whose predicates occurs in Ex
    rem_pred_rules(Rules,LearnPred,SRules1),
    atom_concat(BaseFileName,'.dislp.aba',DISLPFileName),
    ( SRules1 == [] ->
      ( write('WARNING: disjoint ABALP is tabular -- skip '), nl )
    ;
      (
        tell(DISLPFileName),
        print_abaf(Facts,SRules1,Contr),
        told,
        write('disjoint ABALP: '), nl,
        write('  Rules:   '), length(SRules1,SRules1L), write(SRules1L), nl
      )
    ), 
    %%% TAB_ABALPB - remove all rules
    atom_concat(BaseFileName,'.tablp.aba',TABLPFileName),
    tell(TABLPFileName),    
    print_abaf(Facts,[],[]),
    told,
    random_five_fold(SEp, EpRP),
    random_five_fold(SEn, EnRP),
    atom_concat(BaseFileName,'.5fCV.pl',FileName),
    tell(FileName),
    write('bk(\''), write(GENLPFileName), write('\').'), nl,
    write('bk(\''), write(DISLPFileName), write('\').'), nl,
    write('bk(\''), write(TABLPFileName), write('\').'), nl,
    write_5fcv(1,EpRP,EnRP),
    told.

%
select_learnable_pred(Rules,LPreds) :-
    findall(P/1,(member((H,_),Rules),functor(H,P,1)),Preds),
    sort(Preds,SPreds),
    length(SPreds,NPreds),
    Nmax is min(NPreds,10),
    random_between(1,Nmax,TBL),
    n_random_select(TBL,SPreds,LPreds).


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
    write(fold(I,SEp,SEn,FREp,FREn)), write('.'), nl,
    I1 is I+1,
    write_5fcv(I1,EpRP,EnRP).

%%%
tcgen(M,BKsize,E) :-
  try(50,export_predictor_abalpb(M,BKsize,E)),
  !.
tcgen(M,BKsize,E) :-
   write('WARNING: '), write(tcgen(M,BKsize,E)), write('failed 10 times!'), nl.      