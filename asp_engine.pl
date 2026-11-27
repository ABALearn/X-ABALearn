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

rote_lerning_solver(Ri,Ep0,En0,Ep,En,Ls, Cs1) :-
    asp(Ri,Ep0,En0,Ep,En,Ls, S),
    compute_as(S, Cs),
    (   Cs == none
    ->  (   abalearn_log(info,write('rote_lerning_solver result: bottom!')),
            fail
        )
    ;   filter(Cs,Cs1)
    ).

% filter(+As,-As1)
% As1 has an atom p(...) for each atom p_P(...) in As, in the same order;
% atoms whose predicate does not end in _P are dropped.
filter([],[]).
filter([A|As],As1) :-
    (   A =.. [P_P|Args],
        atom_concat(P,'_P',P_P)
    ->  (   A1 =.. [P|Args],
            As1 = [A1|As2]
        )
    ;   As1 = As2
    ),
    filter(As,As2).

% compute_as(+Rs, -Cs)
% Computes the consequences Cs of the rules Rs, according to the learning mode:
%   brave    - Cs is the last (optimal) answer set
%   cautious - Cs is a non-empty ordered subset of the gi/1 arguments in the
%              first answer set that is not an answer set of Rs; other such
%              subsets are returned on backtracking
% Cs is none if Rs is unsatisfiable; fails if clingo stops with no answer set
% for another reason (status unknown or none, see clingo.pl).
compute_as(Rs, Cs) :-
    lopt(learning_mode(brave)),
    !,
    dump_rules(Rs),
    clingo_last_answer(E,Status),
    (   memberchk(Status,[optimum,satisfiable])
    ->  (   Cs = E,
            delete_stderr_log
        )
    ;   (   Status == unsatisfiable,
            Cs = none
        )
    ).
compute_as(Rs, Cs) :-
    lopt(learning_mode(cautious)),
    !,
    utl_rules_append(Rs,[directive(show,gi/1)], Rs1),
    dump_rules(Rs1),
    clingo_answer(E1,Status1),
    (   Status1 == satisfiable
    ->  (   dump_rules(Rs),
            clingo_all_answers(Es,Status),
            (   Status == satisfiable
            ->  (   maplist(sort,Es,Os),
                    diffall([E1],Os,Cs),
                    delete_stderr_log
                )
            ;   (   Status == unsatisfiable,
                    Cs = none
                )
            )
        )
    ;   (   Status1 == unsatisfiable,
            Cs = none
        )
    ).

delete_stderr_log :-
    (   exists_file('clingo.stderr.log')
    ->  delete_file('clingo.stderr.log')
    ;   true
    ).

:- use_module(library(process)).

% clingo_answer(-E,-Status)
% First answer set of asp.clingo (no optimization), with Status:
%   satisfiable   - SATISFIABLE: E is an answer set
%   unsatisfiable - UNSATISFIABLE: there is no answer set, E is none
%   unknown       - UNKNOWN: clingo stopped because of an error (e.g. a syntax
%                   error or a missing file; see the stderr log), E is none
%   none          - no status line: clingo could not be run, E is none
clingo_answer(E,Status) :-
    clingo_run('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore -n1 2>> clingo.stderr.log',first, E,Status).

% clingo_last_answer(-E,-Status)
% Last (optimal) answer set of asp.clingo, with Status:
%   optimum       - OPTIMUM FOUND: the search finished, E is optimal
%   satisfiable   - SATISFIABLE: E is the best found so far (e.g. the time
%                   limit was hit)
%   unsatisfiable - UNSATISFIABLE: there is no answer set, E is none
%   unknown       - UNKNOWN: no answer set was found before the time limit,
%                   or clingo stopped because of an error (e.g. a syntax
%                   error or a missing file; see the stderr log), E is none
%   none          - no status line: clingo could not be run, E is none
clingo_last_answer(E,Status) :-
    clingo_run('clingo ${ASP_INCL} asp.clingo --out-ifs=, --quiet=1 --time-limit=${CLINGO_TIME_LIMIT} 2>> clingo.stderr.log',last, E,Status).

% clingo_all_answers(-Es,-Status)
% All answer sets of asp.clingo (no optimization), in the order clingo prints
% them, with Status as in clingo_answer/2; Es is none if there is none.
clingo_all_answers(Es,Status) :-
    clingo_run('clingo ${ASP_INCL} asp.clingo --out-ifs=, --opt-mode=ignore -n0 2>> clingo.stderr.log',all, Rs,Status),
    (   Rs == none
    ->  Es = none
    ;   reverse(Rs,Es)
    ).

% clingo_run(+Cmd,+Which, -E,-Status)
% Runs the shell command Cmd (a clingo call) and returns the answer sets
% printed, each as a list of atoms: with Which first or last, E is the first
% or last answer set; with Which all, E is the list of all of them, the last
% one first. E is none if there is none. Status is optimum, satisfiable,
% unsatisfiable, unknown or none (see clingo_last_answer/2).
% At verbosity debugging, clingo's raw output is also saved to cc.clingo.
clingo_run(Cmd,Which, E,Status) :-
    process_create(path(sh),['-c',Cmd],[stdout(pipe(Out)),process(Pid)]),
    open_save('cc.clingo', Save),
    call_cleanup(scan_lines(Out,Which,Save,none,none, E,Status),
                 (   close(Out),
                     process_wait(Pid,_),
                     close_save(Save)
                 )).

% open_save(+File, -Save)
% Save is a stream on File if verbosity is at least debugging, none otherwise.
open_save(File, Save) :-
    lopt(verbosity(V)),
    verbosity_value(debugging,D),
    V >= D,
    !,
    open(File,write,Save).
open_save(_, none).

% scan_lines(+In,+Which,+Save,+E0,+S0, -E,-S)
% Reads clingo's output line by line: E is the first or last answer set, or
% the list of all of them, the last one first (Which; none if absent), S is
% optimum, satisfiable, unsatisfiable, unknown or none (no status line).
scan_lines(In,Which,Save,E0,S0, E,S) :-
    read_line_to_string(In,L),
    (   L == end_of_file
    ->  (   E = E0,
            S = S0
        )
    ;   (   save_line(Save,L),
            scan_line(L,In,Which,Save,E0,S0, E1,S1),
            scan_lines(In,Which,Save,E1,S1, E,S)
        )
    ).

% the line after "Answer:" holds the atoms, separated by commas;
% with first, only the first answer set is kept; with last, each new one
% replaces the previous one; with all, each new one is added in front
scan_line(L,In,Which,Save,E0,S, E,S) :-
    string_concat("Answer:",_,L),
    !,
    read_line_to_string(In,AL),
    save_line(Save,AL),
    (   Which == first,
        E0 \== none
    ->  E = E0
    ;   (   atomic_list_concat(['[',AL,']'],AS),
            term_string(A,AS),
            add_answer(Which,A,E0, E)
        )
    ).
scan_line(L,_,_,_,E,_, E,optimum) :-
    string_concat("OPTIMUM FOUND",_,L),
    !.
% each status test is on a prefix, so UNSATISFIABLE never matches SATISFIABLE
scan_line(L,_,_,_,E,_, E,unsatisfiable) :-
    string_concat("UNSATISFIABLE",_,L),
    !.
scan_line(L,_,_,_,E,_, E,satisfiable) :-
    string_concat("SATISFIABLE",_,L),
    !.
scan_line(L,_,_,_,E,_, E,unknown) :-
    string_concat("UNKNOWN",_,L),
    !.
scan_line(_,_,_,_,E,S, E,S).

% add_answer(+Which,+A,+E0, -E)
% E is E0 updated with the new answer set A
add_answer(all,A,none, [A]) :-
    !.
add_answer(all,A,E0, [A|E0]) :-
    !.
add_answer(_,A,_, A).

save_line(none,_) :-
    !.
save_line(Save,L) :-
    writeln(Save,L).

close_save(none) :-
    !.
close_save(Save) :-
    close(Save).


%%%%%%%
rote_lerning_solver___(Ri,Ep0,En0,Ep,En,Ls, Cs1) :-
  asp(Ri,Ep0,En0,Ep,En,Ls, S),
  compute_conseq(S, Cs),
  ( Cs == [] ->
    ( abalearn_log(info,write('rote_lerning_solver result: bottom!')), fail )
  ;
    filter(Cs,Cs1)
  ).
%
% filter([],[]).
% filter([A|As],[A1|As1]) :-
%   findall(Atom2, ( member(Atom1,A), Atom1 =.. [P_P|Args], atom_concat(P,'_P',P_P), Atom2 =.. [P|Args] ), A1),
%   filter(As,As1).

% write the computed consequences (read from cc.clingo) as a prolog list L into cc.pl
compute_conseq(Rs, Cs) :-
  lopt(learning_mode(brave)),
  % write rules to file
  dump_rules(Rs),
  % invoke clingo to compute the consequences of Rs and write them to cc.clingo
  shell('clingo ${ASP_INCL} asp.clingo --out-ifs=, --quiet=1 --time-limit=${CLINGO_TIME_LIMIT} > cc.clingo 2>> clingo.stderr.txt',_),
  shell('cat cc.clingo | grep \'^OPTIMUM FOUND\\|^SATISFIABLE\'',EXIT_CODE),
  EXIT_CODE == 0, % exit status of grep: 0 stands for 'One or more lines were selected.'
  !,
  shell('cat cc.clingo | grep -A1 \'^Answer:\' |  awk \'/Answer:/ {f=NR}; f && NR==f+1 { last = $0 } END { print "[" last "]." }\' > cc.pl'),
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