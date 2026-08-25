% This file is part of the ABALearn project.
% Copyright (C) 2023, 2026  The ABALearn's Authors

% This program is free software: you can redistribute it and/or modify
% it under the terms of the GNU General Public License as published by
% the Free Software Foundation, either version 3 of the License, or
% (at your option) any later version.

% This program is distributed in the hope that it will be useful,
% but WITHOUT ANY WARRANTY; without even the implied warranty of
% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
% GNU General Public License for more details.

% Rote Learning procedures

% roLe(+Ri,+Ep0,+En0,+Ep,+En, -RL,-Ro)
roLe(Ri,Ep0,En0,Ep,En, RLRs,Ro) :-
  learnable_predicates(Ri,Ep, Ls),
  % compute the set of sets representing solutions to the learning problem
  rote_lerning_solver(Ri,Ep0,En0,Ep,En,Ls, AsList), % fails if no sol. to learning prob. can be found 
  member(As, AsList), % As is set of atoms whose predicates occur in Ls                 
  findall(R, ( member(A,As), e_rote_learn(A,R) ), RLRs),
  % add learnt positive examples and contraries to Ri
  aba_ni_rules_append(Ri,RLRs,Ri1),
  %%% init greedy utility predicates
  ( lopt(folding_selection(mgr)) -> 
    ( utl_rules_append(Ri1,[gf([])],Ri2), init_mgr(Ri2,RLRs, Ro) ) 
  ; 
    Ro=Ri1 
  ).


% e_rote_learn(+E, -R)
e_rote_learn(E, R) :- 
  new_rule(E,[], R),
  write('ert: '), show_rule(R), nl.

% learnable_predicates(+Af,+Ep, -Ls)
learnable_predicates(Af,Ep, Ls) :-
  findall(P/N, ( member(E,Ep), functor(E,P,N) ), P1), 
  aba_cnts(Af, Cs), aba_asms(Af, As), 
  findall(P/N, ( member(contrary(_,C),Cs), functor(C,P,N) ), CPs),
  findall(P/N, ( member(assumption(A),As), functor(A,P,N) ), APs),
  findall(P/N, ( member(P/N,CPs), \+ member(P/N,APs) ), P2),
  append(P1,P2,Ps),
  sort(Ps,Ls).