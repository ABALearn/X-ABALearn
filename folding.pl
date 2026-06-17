% This file is part of the ABALearn project.
% Copyright (C) 2023, 2024  The ABALearn's Authors

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

:- use_module(library(dialect/hprolog),[ memberchk_eq/2 ]).
:- use_module('asp_utils').

:- dynamic tokens/1.
tokens(1).

% folding(+Ri,+R, -F)
% Rs: rules for folding, and
% F is the result of applying folding to R
% nd (w/tokens)
folding(Ri,R, F) :-
  copy_term(R,CpyR), 
  rule_hd(CpyR,H), rule_bd(CpyR,Ts), 
  folding_aux(Ri,H,Ts, Fs),
  new_rule(H,Fs,F).
% folding_aux/4
folding_aux(Ri,H,Ts, Fs) :-
  lopt(folding_mode(nd)),
  abalearn_log(finest,( write(' begin nd folding'), nl )), 
  tokens(T),
  fold_nd(T,Ri,H,Ts, Fs).
% greedy
folding_aux(Ri,_H,Ts, Fs) :-
  lopt(folding_mode(greedy)),
  abalearn_log(finest,( write(' begin greedy folding'), nl )), 
  fold_greedy(Ri,Ts, Fs),
  !.   
% all
folding_aux(Ri,_H,Ts, Fs) :-
  lopt(folding_mode(all)),
  abalearn_log(finest,( write(' begin all folding'), nl )), 
  fold_all(Ri,[],Ts,[], Fs).
% lazy
folding_aux(Ri,_H,Ts, Fs) :-
  lopt(folding_mode(lazy)),
  abalearn_log(finest,( write(' begin lazy folding'), nl )), 
  fold_lazy(Ri,Ts, Fs).  

% fold_nd(+T,+Rs,+H,+Ts, -Fs)
% T: tokens for folding
% Rs: rules for folding
% H: head of the clause to be folded
% Ts: To be folded
% Fs: result
% non-deterministic
fold_nd(T,Rs,H,Ts, Fs) :-
  fold_nd_wtc(T,Rs,H,[],Ts, Zs,T1),
  fold_nd_aux(T1,Rs,H,Zs, Fs).
% fold_nd auxiliary predicate
fold_nd_aux(_,_,_,Fs, Fs).
fold_nd_aux(T,Rs,H,[T|Ts], Fs) :-
  fold_nd(T,Rs,H,[T|Ts], Fs).
fold_nd_aux(T,Rs,H,Ts, Fs1) :-
  nselect(P,Ts, E,R),
  fold_nd(T,Rs,H,R, Fs),
  combine(P,E,Fs, Fs1). 

% nselect(+P,+Ts, -E,-R)
% Ts is a list consisting of at least two elements,
% E is the element of Ts at position P, and
% R is Ts without E 
nselect(I,[H1,H2|T], E,R) :-
  nth1(I,[H1,H2|T], E,R).

% combine(+P,+E,+Fs, -Fs1)
% Fs1 is the result of adding E into Fs at position P
combine(P,E,F,C) :-
  combine_aux(1,P,E,F,[], C).
% combine auxiliary predicate
combine_aux(I,P,E,F,CI, CO) :-
  I==P,
  !,
  append(CI,[E|F],CO).
combine_aux(I,P,E,[H|T],CI, CO) :-
  I < P,
  J is I+1,
  append(CI,[H],CI1),
  combine_aux(J,P,E,T,CI1, CO).

% --------------------------------
% fold_nd_wtc(+C,+Rs,+H,+Fs,+Ts, -Zs,Co) -- fold_nd with token counter
% C: tokens for folding
% Rs: rules for folding
% H: head of the clause to be folded
% Fs: already Folded
% Ts: To be folded
% Zs: result
% Co: tokens left for folding (used by fold_nd_aux)
fold_nd_wtc(C,_,_,Fs,[], Fs,C) :-
  C>=0,
  write(' '), write(C), write(': DONE'), nl.
fold_nd_wtc(C,Rs,H,FsI,[T|Ts], FsO,Co) :-
  C>=1,
  select_rule(Rs,T,R1),    % R1 is a (copy of a) clause in Rs that can be used for folding T
  % select_rule sorts the elements in the body so that its head matches T   
  rule_hd(R1,I), rule_hd(R1,F), rule_bd(R1,[T|As]), 
  write(' '), write(C), write(': folding '), show_term([T|Ts]), write(' with '), write(I), write(': '), show_rule(R1), nl,
  aba_asms(Rs,Asms),
  match(As,Ts,Asms, _,NewTs,ResTs), % NewTs consists of equalities in As that do not match with any element in Ts  
  % check if new elements to be folded bind variables occurring elsewhere
  term_variables((H,FsI,ResTs),V1),
  term_variables(NewTs,V2),
  empty_intersection(V2,V1),
  append(ResTs,NewTs, Ts1),
  C1 is C-1,
  fold_nd_wtc(C1,Rs,H,[F|FsI],Ts1, FsO,Co).
fold_nd_wtc(C,_,_,_,[T|Ts], _,C) :-
  C==0,
  write(' '), write(C), write(': FAIL - No more folding tokens left for '), show_term([T|Ts]), nl, fail.

% --------------------------------
% fold_greedy(+Rs,+Tbf,+FsI,+Ids,+N, -FsO)
% Rs: rules for folding
% Tbf: To be folded
% FsO: result
fold_greedy(Rs,Tbf, FsO) :-
  % retrieve folding w/table and the identifiers 
  utl_rules_memberchk(fwt(FwT),Rs),
  fold_greedy(Rs,FwT,Tbf,[],1, FsO).
% FsI: accumulator of foldings perfomed so far
% N: position in Ts of the element to be folded
fold_greedy(Rs,FwT,Tbf,FsI,N, FsO) :-
  % T is the element to be folded
  nth1(N,Tbf,T),
  !,
  abalearn_log(debugging,(  
    copy_term((Tbf,T),(CpyTbf,CpyT)), numbervars(CpyTbf,0,_), write(' sel. '), write(CpyT), nl
  )),  
  % atom to be folded
  ftw_term_key(T,K),
  % retrive ids of rules for folding
  ftw_key_ids(K,FwT,TIds),
  % apply folding to Tbf
  fold_greedy_aux(Rs,Tbf,FsI,TIds, Tbf1,FsI1),
  % fold the (N+1)-th element in Tbf1 
  N1 is N+1,
  fold_greedy(Rs,FwT,Tbf1,FsI1,N1, FsO).
fold_greedy(_Rs,_FwT,_Tbf,Fs,_N, SFs) :-
  sort(Fs,SFs),
  abalearn_log(finest,( write(' '), write('DONE'), nl)).
%
fold_greedy_aux(_Rs,Tbf,Fs,[], Tbf,Fs).
fold_greedy_aux(Rs,Tbf,FsI,[I|Is], TbfO,FsIO) :-
  ( lopt(folding_space(bk)) -> (rlid(J), I<J) ; true ), 
  rule_id(R,I), rule_hd(R,H), rule_bd(R,B),
  % take any rule in Rs whose identifier belongs to IDs
  aba_p_rules_memberchk(R,Rs), 
  % make a copy of the rule
  copy_term((H,B),(CpyH,CpyB)),
  % match the body of R with Tbf
  aba_asms(Rs,Asms),
  match(CpyB,Tbf,Asms, M,NewTbf,_ResTbf),
  % check if new elements to be folded bind variables occurring elsewhere
  term_variables(M,V1), term_variables(NewTbf,V2), empty_intersection(V1,V2),
  !,
  abalearn_log(debugging,(  
    copy_term((Tbf,CpyH,CpyB),(CpyTbf,CpyH1,CpyB1)), numbervars((CpyTbf,CpyH1,CpyB1),0,_), 
    write(' folding '), write(CpyTbf), write(' with '), write(I), write(': '),
    write(CpyH1), write(' <- '), write(CpyB1), nl
  )),
  % add new equalities to Tbf
  ( memberchk_eq(CpyH,FsI) -> ( FsI1=FsI, Tbf1=Tbf ) ; ( FsI1=[CpyH|FsI], append(Tbf,[CpyH|NewTbf],Tbf1) ) ),
  fold_greedy_aux(Rs,Tbf1,FsI1,Is, TbfO,FsIO).
fold_greedy_aux(Rs,Tbf,FsI,[_|Is], Tbf1,FsI1) :-
  % I can't be used for folding, skip
  fold_greedy_aux(Rs,Tbf,FsI,Is, Tbf1,FsI1).

% --------------------------------
% fold_all(Rs,As,Ts,FsI, FsO)
% Rs: rules for folding
% As: folded elements
% Ts: elements to be folded
% FsI: already folded
% FsO: fold result
fold_all(Rs,As,[T|Ts],FsI, FsO) :- 
  select_rule(Rs,T,R),        % R is a (copy of a) clause in Rs that can be used for folding T
  rule_hd(R,I), rule_hd(R,H), rule_bd(R,[T|Bs]), % select_rule sorts the elements in the body so that its head matches T 
  write(' folding '), show_term([T|Ts]), write(' with '), write(I), write(': '), show_rule(R), nl,
  aba_asms(Rs,Asms),
  match(Bs, As,Asms, _Ms,RBs,_Rs), % match all the elements that have already been folded (As)
                                   % RBs are elements in the body of the rule R matching with no element in As 
  match(RBs,Ts,Asms, TMs,New,RTs), % match all the elements that have not yet been folded (Ts)
                                   % TMs is Ts \ elements in Ts that do not match any element in RBs
  \+ memberchk_eq(H,FsI),     % H does not belong to the list of elements obtained by folding
  append(As,TMs,As1),
  append(New,RTs,NewTs),
  %append(FsI,[H],FsI1),      % TODO: different order of folding
  FsI1=[H|FsI],
  fold_all(Rs,[T|As1],NewTs,FsI1, FsO).
% TODO: move this case (repeated folding) in a different predicate 
%fold_all(Rs,As,[_|Ts],FsI, FsO) :- 
%  fold_all(Rs,As,Ts,FsI, FsO).
fold_all(_,[_|_],[],Fs, Fs).  % [] nothing left to be folded, [_|_] something has been folded
                              % Note fold is called with As=[]

% R is a rule in Rs that can be used to fold T
select_rule(Ri,T,R) :-
  % retrieve folding w/table
  utl_rules_memberchk(fwt(FwT),Ri),
  % atom to be folded
  ftw_term_key(T,K),
  % retrive ids of rules for folding
  memberchk((K,IDs),FwT),
  % take any rule in Rs whose identifier belongs to IDs
  member(I,IDs), rule_id(M,I), 
  aba_p_rules_memberchk(M,Ri), 
  ( lopt(folding_space(bk)) -> (rlid(J), I<J) ; true ), 
  rule_hd(M,H), rule_bd(M,Bs),  
  % select any term B in the body of Bs
  select(B,Bs,Bs1),
  % check if B is more general than T
  subsumes_term(B,T),
  % make a copy of the rule
  copy_term((H,B,Bs1),(CpyH,CpyB,CpyBs)),
  % create the new rule, where the head of the body is (the copy of) the matching element
  rule_id(R,I), rule_hd(R,CpyH), rule_bd(R,[CpyB|CpyBs]).


% match(As,Bs,Asms, Ms,ARs,BRs) holds iff Ms consists of elements in As that 
% have been unified with a (possibly) more specific element in Bs.
% ARs and BRs consists of elements in As and Bs, respectively, not in Ms
match([],Bs,_Asms, [],[],Bs).
match([A|As],Bs,Asms, AMs,ARs,BRs) :- 
  match([A|As],Bs,Asms, AMs,BMs,ARs,BRs),
  subsumes_term(AMs,BMs),
  !,
  AMs=BMs.

% 
match([],Bs,_Asms, [],[],[],Bs).
match([A|As],Bs,Asms, [A|AMs],[B|BMs],ARs,BRs) :- 
  select_subsumed(A,Bs, B,Bs1),
  match(As,Bs1,Asms, AMs,BMs,ARs,BRs).
match([X=Y|As1],Bs,Asms, AMs,BMs,[X=Y|ARs],BRs) :-
  match(As1,Bs,Asms, AMs,BMs,ARs,BRs).
match([Asm|As1],Bs,Asms, AMs,BMs,ARs,BRs) :-
  copy_term(Asm,CpyAsm),
  memberchk(CpyAsm,Asms), % Asm is an assumption -- skip
  match(As1,Bs,Asms, AMs,BMs,ARs,BRs).  

% empty_intersection/2
empty_intersection([],_).
empty_intersection([E|_],L2) :- 
  memberchk_eq(E,L2),
  !,
  fail.
empty_intersection([_|Es],L2) :- 
  empty_intersection(Es,L2).

% --------------------------------
% fold_lazy(Rs,Ts, FsO)
% Rs: rules for folding
% Ts: elements to be folded
% FsO: fold result
fold_lazy(Rs,Ts, FsO) :-
  fold_lazy(Rs,Ts,1, FsO).
% fold_lazy/4
% L: max length of FsO
:- dynamic ok/0.
fold_lazy(Rs,Ts,L, FsO) :- 
  %fold_lazy(Rs,[],Ts,[],L, FsO). % folding of length L
  fold_lazy_new(Rs,[],Ts,[],[],L, FsO). % folding of length L  
fold_lazy(Rs,Ts,L, FsO) :-
  L1 is L+1,
  %fold_lazy(Rs,[],Ts,[],L, _),
  fold_lazy_new(Rs,[],Ts,[],[],L, _),
  nl, write('* folding reboot: increasing length to: '), write(L1), nl, nl,
  !,
  fold_lazy(Rs,Ts,L1, FsO).

% --------------------------------
% fold_lazy(Rs,As,Ts,FsI,C, FsO)
% As: folded elements
% FsI: accumulator of foldings perfomed so far
fold_lazy(Rs,As,[T|Ts],FsI,C, FsO) :-
  C>=1,
  select_rule(Rs,T,R),        % R is a (copy of a) clause in Rs that can be used for folding T
  % select_rule sorts the elements in the body so that its head matches T
  rule_id(R,I), rule_hd(R,H), rule_bd(R,[T|Bs]),
  abalearn_log(finest,(  
    copy_term(([T|Ts],R),(CpyTs,CpyR)), numbervars((CpyTs,CpyR),0,_), 
    write(' folding '), write(CpyTs), write(' with '), write(I), write(': '), write(CpyR), nl
  )),
  aba_asms(Rs,Asms),
  match(Bs, As,Asms, _Ms,RBs,_Rs), % match all the elements that have already been folded (As)
                                   % RBs are elements in the body of the rule R matching with no element in As 
  match(RBs,Ts,Asms, TMs,New,RTs), % match all the elements that have not yet been folded (Ts)
                                   % TMs is Ts \ elements in Ts that do not match any element in RBs
  append(As,TMs,As1),
  append(New,RTs,NewTs),
  % TODO: to be generalized for folding w/multiple clauses
  ( memberchk_eq(H,FsI) -> (FsI1=FsI, C1=C) ; (FsI1=[H|FsI], C1 is C-1) ),
  fold_lazy(Rs,[T|As1],NewTs,FsI1,C1, FsO).
fold_lazy(_,_,[],Fs,C, Fs):- % [] nothing left to be folded, [_|_] something has been folded
  C=0.                       % Note fold is called with As=[]
fold_lazy(Rs,As,[],Fs,C, FsO) :-
  C>=1, 
  append(As,Fs,Ts), sort(Ts,Ss), 
  fold_lazy(Rs,[],Ss,Fs,C, FsO).

% --------------------------------------
% fold_lazy_new(Rs,As,Ts,FsI,UsI,C, FsO)
% As: folded elements
% FsI: accumulator of foldings perfomed so far
fold_lazy_new(Rs,As,[T|Ts],FsI,UsI,C, FsO) :-
  C>=1,
  select_rule_new(Rs,T,UsI, R),        % R is a (copy of a) clause in Rs that can be used for folding T
  % select_rule sorts the elements in the body so that its head matches T
  rule_id(R,I), rule_hd(R,H), rule_bd(R,[T|Bs]),
  abalearn_log(finest,(  
    copy_term(([T|Ts],R),(CpyTs,CpyR)), numbervars((CpyTs,CpyR),0,_), 
    write(' folding '), write(CpyTs), write(' with '), write(I), write(': '), write(CpyR), nl
  )),
  aba_asms(Rs,Asms),
  match(Bs, As,Asms, _Ms,RBs,_Rs), % match all the elements that have already been folded (As)
                                   % RBs are elements in the body of the rule R matching with no element in As 
  match(RBs,Ts,Asms, TMs,New,RTs), % match all the elements that have not yet been folded (Ts)
                                   % TMs is Ts \ elements in Ts that do not match any element in RBs
  append(As,TMs,As1),
  append(New,RTs,NewTs),
  %%%
  fold_lazy_new_aux(T,TMs,I,H,As1,NewTs,FsI,UsI,C, As2,NewTs2,FsI1,UsI1,C1),
  %%%
  fold_lazy_new(Rs,As2,NewTs2,FsI1,UsI1,C1, FsO).
fold_lazy_new(_,_,[],Fs,_Us,C, Fs):- % [] nothing left to be folded, [_|_] something has been folded
  C==0.

% R is a rule in Rs that can be used to fold T
select_rule_new(Ri,T,Fs, R) :-
  % retrieve folding w/table
  utl_rules_memberchk(fwt(FwT),Ri),
  % atom to be folded
  ftw_term_key(T,K),
  % retrive ids of rules for folding
  memberchk((K,IDs),FwT),
  % select a ruleID to fold T
  select_rule_new_aux(IDs,T,Fs, I),
  rule_id(M,I),
  % retrieve rule with ID M 
  aba_p_rules_memberchk(M,Ri), 
  ( lopt(folding_space(bk)) -> (rlid(J), I<J) ; true ), 
  rule_hd(M,H), rule_bd(M,Bs),
  % select any term B in the body of Bs
  select(B,Bs,Bs1),
  % check if B is more general than T
  subsumes_term(B,T),
  % make a copy of the rule
  copy_term((H,B,Bs1),(CpyH,CpyB,CpyBs)),
  % create the new rule, where the head of the body is (the copy of) the matching element
  rule_id(R,I), rule_hd(R,CpyH), rule_bd(R,[CpyB|CpyBs]).

%
%select_rule_new_aux([ID|_],T,Fs, ID) :-  
%  \+ memberchk_eq((T,ID),Fs).
select_rule_new_aux([ID|_],T,Fs, ID) :-
  gt_all(ID,T,Fs).   
select_rule_new_aux([_|IDs],T,Fs, ID) :-    
  select_rule_new_aux(IDs,T,Fs, ID).

%
gt_all(ID,T,Fs) :-
  member((T1,ID1),Fs), T1==T,
  ID < ID1,
  !,
  fail.
gt_all(ID,T,Fs) :-
  \+ memberchk_eq((T,ID),Fs).

fold_lazy_new_aux(_T,_TMs,_I,H,As,NewTs,FsI,UsI,C, As,NewTs,FsI,UsI,C) :-
  memberchk_eq(H,FsI),
  !.
%
fold_lazy_new_aux(T,TMs,I,H,As1,NewTs,FsI,UsI,C, As2,NewTs2,FsI1,UsI1,C1) :-
  update_folds([T|TMs],I,UsI, UsI1),
  ( 
    (As2 = [T|As1], NewTs1 = NewTs) 
  ; 
    (As2 = As1, NewTs1 = [T|NewTs]) 
  ),
  ( %TODO: replace append
    ( append(FsI,[H],FsI1), NewTs1 = NewTs2) ; 
    ( FsI1=FsI, append(NewTs1,[H],NewTs2) ) ; 
    ( append(FsI,[H],FsI1), append(NewTs1,[H],NewTs2) ) 
  ),
  C1 is C-1.

%
update_folds([],_,UsI, UsI). 
update_folds([T|Ts],I,UsI, UsO) :- 
  update_folds(Ts,I,[(T,I)|UsI], UsO).  
