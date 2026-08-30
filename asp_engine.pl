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
    [  entails/5
    ,  extension/2
    ,  extension/3
    ,  extensions/2
    ,  extensions/3    
    ,  rote_lerning_solver/7
    ,  satisfiable/1
    ]).

%
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
compute_conseq(Rs, [S1]) :-
  lopt(learning_mode(cautious)),
  utl_rules_append(Rs,[directive(show,gi/1)], Rs1),
  % write rules to file
  dump_rules(Rs1),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'',EXIT_CODE1),
  EXIT_CODE1 == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all(Cs1), % Cs is a singleton  
  seen, 
  %%%%
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore -n0 > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !, 
  see('cc.pl'),
  % read 'cc.clingo' and assert it into the database
  read_all_ord(Cs), 
  seen,
  diffall(Cs1,Cs,S1),
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
% assert all terms from file
read_all_ord([O|Os]) :-
  read(A),
  A \== end_of_file,
  !,
  sort(A,O),
  read_all_ord(Os).
read_all_ord([]).

%
diffall([Cs1],Cs,O) :-
  findall(F,member(gi(F),Cs1),FCs), 
  sort(FCs,S),
  !, 
  ord(S,O),
  \+ memberchk(O,Cs).
  
%
ord([H|_],[H]).
ord([_|T],S) :-
  ord(T,S).
ord([H|T],[H|S]) :-
  ord(T,S).

% -----------------------------------------------------------------------------
% R entails all elements in Ep and R does not entail any element of En
entails(R,Ep0,En0,Ep,En) :-
  lopt(learning_mode(brave)),
  asp(R,Ep0,En0,Ep,En,[], A),
  % write rules to file
  dump_rules(A),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'  > /dev/null',EXIT_CODE),
  !,
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'
entails(R,Ep0,En0,Ep,En) :-
  lopt(learning_mode(cautious)),
  asp(R,Ep0,En0,Ep,En,[], A),
  % write rules to file
  dump_rules(A),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore > cc.clingo 2>> clingo.stderr.txt',_EXIT_CODE),
  shell('cat cc.clingo | grep \'^UNSATISFIABLE\'  > /dev/null',EXIT_CODE),
  !,
  EXIT_CODE == 0. % exit status of grep: 0 stands for 'One or more lines were selected.'  

% -----------------------------------------------------------------------------
% extension/2  
extension(ABAF, E) :-
  extension(ABAF,[], E).
% extension/3
extension(ABAF,Ps, E) :-
  % for each P/N in Ps, add a show directive
  % if Ps is empty, then the extension includes all the predicates 
  findall(directive(show,P/N),member(P/N,Ps),Sw),
  utl_rules_append(ABAF,Sw,Rs),
  % create the ASP encoding
  asp(Rs,[],[],[],[],[], RsASP),
  % write rules to file
  dump_rules(RsASP),
  % invoke clingo to compute the answer sets of RsASP and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore -n1 > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'',EXIT_CODE),
  !,
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  see('cc.pl'),
  % read 'cc.clingo' - read first extension
  read_all([E]),
  seen.

% extension/2  
extensions(ABAF, Es) :-
  extensions(ABAF,[], Es).
% extension/3
extensions(ABAF,Ps, Es) :-
  % for each P/N in Ps, add a show directive
  % if Ps is empty, then the extension includes all the predicates 
  findall(directive(show,P/N),member(P/N,Ps),Sw),
  utl_rules_append(ABAF,Sw,Rs),
  % create the ASP encoding
  asp(Rs,[],[],[],[],[], RsASP),
  % write rules to file
  dump_rules(RsASP),
  % invoke clingo to compute the answer sets of RsASP and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore -n0 > cc.clingo 2>> clingo.stderr.log',_),
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { print "[",$0,"]."}\' > cc.pl'),
  shell('cat cc.clingo | grep \'^SATISFIABLE\'',EXIT_CODE),
  !,
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  see('cc.pl'),
  % read 'cc.clingo' (list of extensions)
  read_all(Es),
  seen. 

% -----------------------------------------------------------------------------
% extension/1
satisfiable(ABAF) :-
  extension(ABAF, _). 