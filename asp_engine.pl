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

:- module(clingo,
    [  compute_conseq/2 % compute brave/cautious conseq. and assert them
    ,  entails/5
    ,  rote_lerning_solver/7
    ,  subsumed/6
    ]).


rote_lerning_solver(Ri,Ep0,En0,Ep,En,Ls, Cs1) :-
  asp(Ri,Ep0,En0,Ep,En,Ls, S),
  compute_conseq(S, Cs),
  ( Cs == [] ->
    ( abalearn_log(info,write('rote_lerning_solver result: bottom!')), fail )
  ;
    filter(Cs,Cs1)
  ).
%
filter([],[]).
filter([A|As],[A1|As1]) :-
  findall(Atom2, ( member(Atom1,A), Atom1 =.. [P_P|Args], atom_concat(P,'_P',P_P), Atom2 =.. [P|Args] ), A1),
  filter(As,As1).

% write the computed consequences (read from cc.clingo) as a prolog list L into cc.pl
compute_conseq(Rs, Cs) :-
  lopt(learning_mode(brave)),
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  %shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=optN --quiet=1 > cc.clingo 2>> clingo.stderr.txt',_),
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --quiet=1 --time-limit=${CLINGO_TIME_LIMIT} > cc.clingo 2>> clingo.stderr.txt',_),
  %shell('cat cc.clingo | grep \'^OPTIMUM FOUND\'  > /dev/null',EXIT_CODE), 
  shell('cat cc.clingo | grep \'^OPTIMUM FOUND\\|^SATISFIABLE\'',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !,
  % TODO: assuming one solution
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all(Cs),
  seen,
  shell('rm -f clingo.stderr.log',_).
compute_conseq(Rs, Cs) :-
  lopt(learning_mode(cautious)),
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !,
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all(Cs), % Cs is a singleton
  seen,
  shell('rm -f clingo.stderr.log',_).
compute_conseq(_, []) :-
  shell('cat cc.clingo | grep \'^UNSATISFIABLE\' > /dev/null',EXIT_CODE),
  EXIT_CODE == 0,
  !.
% assert all terms from file
read_all([A|As]) :-
  read(A),
  A \== end_of_file,
  !,
  read_all(As).
read_all([]).

% -----------------------------------------------------------------------------
% Ri subsumes rule R
subsumed(Ri,Ep0,En0,Ep,En, _R) :-
  lopt(learning_mode(brave)),
  !,
  rule_hd(R,H), rule_bd(R,B),
  ic([not H|B],I),
  utl_rules_append(Ri,[I], Ri1),
  % asp w/ic for Ep and En
  asp(Ri1,Ep0,En0,Ep,En,[], Ro),
  % write rules to file
  dump_rules(Ro),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'
subsumed(Ri,Ep0,En0,Ep,En, R) :-
  lopt(learning_mode(cautious)),
  % asp w/ic for Ep and En
  asp(Ri,Ep0,En0,Ep,En,[], Ro),
  % write rules to file
  dump_rules(Ro),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read(As),
  seen,
  copy_term(R,CpyS), rule_hd(CpyS,H), rule_bd(CpyS,B),
  unify_eqs(B),
  !,
  member(H,As).
% subsumed (cautious) predicate
unify_eqs([]).
unify_eqs([V=C|E]) :-
  V=C,
  unify_eqs(E).

% -----------------------------------------------------------------------------
% R entails all elements in Ep and R does not entail any element of En
entails(R,Ep0,En0,Ep,En) :-
  lopt(learning_mode(brave)),
  !,
  asp(R,Ep0,En0,Ep,En,[], A),
  % write rules to file
  dump_rules(A),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'
entails(R,Ep0,En0,Ep,En) :-
  lopt(learning_mode(cautious)),
  !,
  asp(R,[],[],[],[],[], A), % NO ic for positive and negative examples
  dump_rules(A),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore --enum-mode=cautious > cc.clingo 2>> clingo.stderr.log',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  shell('echo \'[\' > cc.pl'),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' | tail -n -1 >> cc.pl'),
  shell('echo \'].\' >> cc.pl'),
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read(As),
  seen,
  append(Ep0,Ep,Ep1), append(En0,En,En1),
  entails_cautious(Ep1,En1,As).
% entails (cautious) utility predicate
entails_cautious([],[],_Cs).
entails_cautious([E|Ep],En,Cs) :-
  member(E,Cs),
  !,
  entails_cautious(Ep,En,Cs).
entails_cautious([],[E|En],Cs) :-
  \+ member(E,Cs),
  !,
  entails_cautious([],En,Cs).
