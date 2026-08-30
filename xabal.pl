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
:- use_module(library(clpfd)).

:- use_module('asp_utils').
:- use_module('asp_engine').

:- consult('rote_learning.pl'),
   consult('gen.pl'),
   consult('io.pl').


:- initialization(set_lopt(folding_mode(lazy))).
:- initialization(set_lopt(folding_selection(any))).
:- initialization(set_lopt(folding_space(all))).
:- initialization(set_lopt(asm_intro(relto(even)))).
:- initialization(set_lopt(learning_mode(brave))).
:- initialization(set_lopt(verbosity(debugging))).
:- initialization(set_lopt(log_stream(user_output))).
:- initialization(set_lopt(post_folding_test_entailment(true))).
:- initialization(set_lopt(clingo_time_limit(180))).

:- initialization(listing(lopt/1)).

% xabal(+BK,+Ep,+En)
% xabal(BK,Ep0,En0,Ep,En)
% BK: file including the background knowledge
% (Ep0) Ep: (already covered) positive examples
% (En0) En: (already covered) negative examples
xabal(BK,Ep,En) :-
  xabal(BK,[],[],Ep,En, _Ro).
xabal(BK,Ep0,En0,Ep,En) :-
  xabal(BK,Ep0,En0,Ep,En, _Ro).  

% xabal(+BK,+Ep,+En, -Ro)
% Ro: learnt ABA framework
xabal(BK,Ep0,En0,Ep,En, Ro) :-
  check_options,
  % initialize solution counter
  retractall(sol_counter(_)),
  assert(sol_counter(0)),
  % initialize tokens (for folding)
  retractall(tokens(_)),
  assert(tokens(1)),
  %%%
  nl, write('Current learning options:'), nl,
  listing(lopt/1),
  %
  read_bk(BK, Rs),
  check_aba(Rs,Ep,En),
  rules_aba_utl(Rs, R1), % partition the list of rules Rs into two sublists ABA and UTL
                         % ABA = rules of the ABA framework
                         % UTL = utility rules (e.g., assumption, contrary)
  init_new_pred_gen(R1), % initialize generator of new assumption names
  xabal_proc(BK,R1,Ep0,En0,Ep,En, Ro).
%
xabal_proc(BK,R1,Ep0,En0,Ep,En, Ro) :-
  ( satisfiable(R1) -> true ; ( write('BK unsat! '), nl, fail ) ),
  %%%
  statistics(runtime,[T1,_]),     % cpu time
  statistics(system_time,[S1,_]), % system time
  statistics(walltime,[W1,_]),    % wall time                     % rules counter
  %%%
  roLe(R1,Ep0,En0,Ep,En, _RL,R2),  % RoLe
  % moved to rote_learning.pl
  %( lopt(folding_selection(mgr)) -> ( utl_rules_append(R2,[gf([])],R3), init_mgr(R3,RL, R4) ) ; R2=R4 ),
  R2=R4,
  genT(R4,Ep0,En0,Ep,En, Ro),     % GEN
  %%%
  statistics(runtime,[T2,_]),     T is T2-T1,   
  statistics(system_time,[S2,_]), S is S2-S1,
  statistics(walltime,[W2,_]),    W is W2-W1,
  nl,
  write('BK size (rules):   '), bksize(BKSize), write(BKSize), nl,
  write('Positive examples: '), length(Ep,EpN), write(EpN), nl,
  write('Negative examples: '), length(En,EnN), write(EnN), nl,
  write('ABA size (rules):  '), 
  aba_rules(Ro,Rules), length(Rules,RulesSize),
  write(RulesSize), nl, 
  write('Learning (CPU,Sys,Wall,CPU+Sys) time: '), 
  write(T), write(','), 
  write(S), write(','), 
  write(W), write(','), Lt is T+S, write(Lt), nl,
  % output files
  ( atom_concat(BKBaseName,'.aba',BK) -> true ; BKBaseName=BK  ),
  atom_concat(BKBaseName,'.sol.aba',Out),
  retract(sol_counter(N)), M is N+1, assert(sol_counter(M)),
  nl, write('Writing solution no. '), write(M), write(' to '), write(Out), nl, nl,
  write_sol(Ro,Out),
  atom_concat(BKBaseName,'.sol.asp',OutASP),
  asp(Ro,[],[],[],[],[], RoASP),
  dump_rules(RoASP,OutASP),
  ( lopt(check_ic) -> 
    ( asp(Ro,Ep0,En0,Ep,En,[], RoASPwIC), atom_concat(BKBaseName,'.sol_chk.asp',OutASPwIC),  dump_rules(RoASPwIC,OutASPwIC) ) 
  ;
    true
  ),
  open('xabal.csv',append,Stream),
  % timestamp
  get_time(TimestampTrStarted),
  stamp_date_time(TimestampTrStarted,DT,'local'),
  format_time(atom(FDT),'%Y-%m-%d %T',DT,'posix'),
  write(Stream,FDT), write(Stream,','),
  % name
  file_base_name(BK,BKName), write(Stream,BKName), write(Stream,','),
  % semantic (if any)
  ( lopt(semantics(Sem)) -> write(Stream,Sem) ; write(Stream,'\'\\N\'') ), write(Stream,','), 
  % BK size
  write(Stream,BKSize), write(Stream,','),
  % pos
  write(Stream,EpN), write(Stream,','),
  % neg
  write(Stream,EnN), write(Stream,','),
  % Out size
  write(Stream,RulesSize), write(Stream,','),
  % time (CPU,Sys,Wall,CPU+Sys)
  write(Stream,T),  write(Stream,','), 
  write(Stream,S),  write(Stream,','), 
  write(Stream,W),  write(Stream,','),
  write(Stream,Lt), write(Stream,'\n'),
  close(Stream).
xabal_proc(_,_,_,_,_,_, _) :-
  sol_counter(N),
  nl, 
  ( N == 0 ->
    abalearn_log(info,write('* No solution found! '))
  ; 
    abalearn_log(info,write('* There are no more solutions! '))
  ).

check_entailment(BK,E,Ps,Ns) :-
  Ep=[],
  En=[],
  check_options,
  % initialize solution counter
  retractall(sol_counter(_)),
  assert(sol_counter(0)),
  % initialize tokens (for folding)
  retractall(tokens(_)),
  assert(tokens(1)),
  %%%
  nl, write('Current learning options:'), nl,
  listing(lopt/1),
  %
  read_bk(BK, Rs),
  check_aba(Rs,Ep,En),
  rules_aba_utl(Rs, Ro), % partition the list of rules Rs into two sublists ABA and UTL
                         % ABA = rules of the ABA framework
                         % UTL = utility rules (e.g., assumption, contrary)
  check_entailment_aux(Ro,E,[],[], Ps,Ns),
  !.
%
check_entailment_aux(_,[],Ps,Ns, Ps,Ns).
check_entailment_aux(R,[E|Es],PsI,NsI, PsO,NsO) :-
  ( entails(R,[],[],[E],[]) ->
    ( Ps1=[E|PsI], Ns1=NsI ) 
  ;
    ( Ps1=PsI, Ns1=[E|NsI] )
  ),
  check_entailment_aux(R,Es,Ps1,Ns1, PsO,NsO). 

%
:- dynamic lopt/1.
set_lopt(folding_mode(nd)) :-
  !,
  retractall(lopt(folding_mode(_))),
  assert(lopt(folding_mode(nd))),
  ( lopt(folding_steps(_)) -> true ; set_lopt(folding_steps(5)) ).
set_lopt(folding_mode(X)) :-
  member(X,[greedy,all,lazy]),
  !,
  retractall(lopt(folding_mode(_))),
  assert(lopt(folding_mode(X))).
set_lopt(folding_steps(X)) :-
  !,
  retractall(lopt(folding_steps(_))),
  assert(lopt(folding_steps(X))).
set_lopt(asm_intro(X)) :-
  member(X,[sechk,relto(true),relto(even)]),
  !,
  retractall(lopt(asm_intro(_))),
  assert(lopt(asm_intro(X))).
set_lopt(learning_mode(X)) :-
  member(X,[brave,cautious]),
  !,
  retractall(lopt(learning_mode(_))),
  assert(lopt(learning_mode(X))).
set_lopt(folding_selection(X)) :-
  member(X,[any,mgr]),
  !,
  retractall(lopt(folding_selection(_))),
  assert(lopt(folding_selection(X))).
set_lopt(check_ic) :-
  !,
  retractall(lopt(check_ic)),
  assert(lopt(check_ic)). 
set_lopt(folding_space(X)) :-
  member(X,[bk,all]),
  !,
  retractall(lopt(folding_space(_))),
  assert(lopt(folding_space(X))).
set_lopt(verbosity(X)) :-
  memberchk(X,[off,error,warning,info,fine,finer,finest,debugging]),
  !,
  retractall(lopt(verbosity(_))),
  verbosity_value(X,V),
  assert(lopt(verbosity(V))).
set_lopt(log_stream(user_output)) :-
  !,
  retractall(lopt(log_stream(_))),
  assert(lopt(log_stream(user_output))).
set_lopt(log_stream(S)) :-
  atomic(S),
  !,
  retractall(lopt(log_stream(_))),
  open(S,write,Stream),
  assert(lopt(log_stream(Stream))).
set_lopt(post_folding_test_entailment(V)) :-
  atomic(V),
  member(V,[true,false]),
  !,
  retractall(lopt(post_folding_test_entailment(_))),
  assert(lopt(post_folding_test_entailment(V))).
set_lopt(semantics(S)) :-
  atomic(S),
  member(S,[adm,com,grd,prf,stb]),
  !,
  retractall(lopt(semantics(_))),
  assert(lopt(semantics(S))),
  working_directory(WD,WD),
  atom_concat(WD,'lib/pi_',WD1),
  atom_concat(WD1,S,S1), atom_concat(S1,'.asp',F),
  setenv('ASP_INCL',F),
  set_semantics_enc.
set_lopt(clingo_time_limit(CTO)) :-
  number(CTO),
  !,
  retractall(lopt(clingo_time_limit(_))),
  assert(lopt(clingo_time_limit(CTO))),
  setenv('CLINGO_TIME_LIMIT',CTO).
set_lopt(X) :-
  throw(wrong_lopt(X)).

%
check_options :- 
  ( ( lopt(semantics(X)), lopt(learning_mode(cautious)) ) -> 
    ( 
      write('>> The options combination '),
      write(lopt(semantics(X))),
      write(' and '),
      write(lopt(learning_mode(cautious))),
      write(' is not supported <<'), nl, 
      halt
    )
  ; 
    true 
  ).  

write_sol(Rs,File) :-
  tell(File),
  % intensional and nonintensional rules
  aba_rules(Rs,R),
  write_rules(R),
  nl,
  % assumptions
  aba_asms(Rs,A),
  % contraries
  aba_cnts(Rs,C),
  append(A,C,AC),
  write_ac(AC),
  told.

% write rule
write_rules([]). 
write_rules([R|Rs]) :-
  is_rule(R),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),  
  rule_hd(CpyR,H), rule_bd(CpyR,B),
  write(H), write(' :- '), write_conj(B),
  write_rules(Rs).
write_rules([_|Rs]) :-
  write_rules(Rs). 

%
write_conj([]) :-
  write('.'), nl.
write_conj([H]) :-
  !,
  write(H), write('.'), nl.
write_conj([H|T]) :-
  write(H), write(', '),
  write_conj(T).

%
write_ac([]).
write_ac([R|Rs]) :-
  R = assumption(_),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),    
  write(CpyR), write('.'), nl,
  write_ac(Rs). 
write_ac([R|Rs]) :-
  R = contrary(_,_),
  !,
  copy_term(R,CpyR),
  numbervars(CpyR,0,_),
  CpyR = contrary(A,_),
  write(CpyR), write(' :- '), write(assumption(A)),  write('.'), nl,
  write_ac(Rs).
write_ac([_|Rs]) :-
  write_ac(Rs). 

%
check_aba(Rules,Ep,_En) :-
  collect_consts(Rules,[], Cs),
  check_ep_consts(Ep,Cs).

%
collect_consts([],Ci, Co) :-
  sort(Ci,Co).
collect_consts([R|Rs],Ci, Co) :-
  rule_bd(R,B),
  !,  
  collect_consts_aux(B,Ci, Ci1),
  collect_consts(Rs,Ci1, Co).
collect_consts([_|Rs],Ci, Co) :-
  collect_consts(Rs,Ci, Co).  
% assumption: rules are normalized
% (i.e., constants occur in the body 
% of rules as equalities of the form 
% Var=constant)
collect_consts_aux([],Ci, Ci).
collect_consts_aux([X=C|Bs],Ci, Cs) :-
  var(X),
  ground(C),
  !,
  collect_consts_aux(Bs,[C|Ci], Cs).
collect_consts_aux([_|Bs],Ci, Cs) :-
  collect_consts_aux(Bs,Ci, Cs).

%
check_ep_consts([],_).
check_ep_consts([E|Es],Ci) :-
  E =.. [_|Args],
  check_ep_consts_aux(Args,Ci),
  check_ep_consts(Es,Ci).

%
check_ep_consts_aux([],_).
check_ep_consts_aux([Arg|Args],Ci) :-
  nonvar(Arg),
  !,
  ( member(Arg,Ci) ->
    check_ep_consts_aux(Args,Ci)
  ;
    ( write('ERROR: unknown constant: '), write(Arg), nl, nl, halt )
  ).
check_ep_consts_aux([Arg|Args],Ci) :-
  var(Arg),
  check_ep_consts_aux(Args,Ci).

% --------------- acceptance test -----------------
test_abaf(ABAF_file,Ep,En) :-
  test_abaf(ABAF_file,[],[],Ep,En).

test_abaf(ABAF_file,Ep0,En0,Ep,En) :-
  read_bk(ABAF_file, ABAF),
  rules_aba_utl(ABAF, ABAF1),
  ( atom_concat(BKBaseName,'.aba',ABAF_file) -> true ; BKBaseName=ABAF_file  ),
  atom_concat(BKBaseName,'.test.csv',TestFile),
  tell(TestFile),
  test_abaf_aux(ABAF1,Ep0,En0,Ep,En),
  told.

test_abaf_aux(_ABAF,_,_,[],[]).      
test_abaf_aux(ABAF,Ep0,En0,[E|Ep],En) :-
  write(E), write(','), write(pos), write(','),
  test_entails(ABAF,Ep0,En0,E,Res),
  write(Res),
  nl,  
  test_abaf_aux(ABAF,Ep0,En0,Ep,En).
test_abaf_aux(ABAF,Ep0,En0,[],[E|En]) :-
  write(E), write(','), write(neg), write(','),
  test_entails(ABAF,Ep0,En0,E,Res),
  write(Res),
  nl,  
  test_abaf_aux(ABAF,Ep0,En0,[],En).
% version that adds the domain rule for the constant occurring in the example 
% test_abaf_aux(_ABAF,_,_,[],[]).      
% test_abaf_aux(ABAF,Ep0,En0,[pos(E,F)|Ep],En) :-
%   write(E), write(','), write(pos), write(','),
%   ex_rules(ABAF,F, ABAFwER),
%   test_entails(ABAFwER,Ep0,En0,E,Res),
%   write(Res),
%   nl,  
%   test_abaf_aux(ABAF,Ep0,En0,Ep,En).
% test_abaf_aux(ABAF,Ep0,En0,[],[neg(E,F)|En]) :-
%   write(E), write(','), write(neg), write(','),
%   ex_rules(ABAF,F, ABAFwER),
%   test_entails(ABAFwER,Ep0,En0,E,Res),
%   write(Res),
%   nl,  
%   test_abaf_aux(ABAF,Ep0,En0,[],En).

%
test_entails(ABAF,Ep0,En0,E,Res) :-
  statistics(runtime,[T1,_]),     % cpu time
  statistics(system_time,[S1,_]), % system time
  statistics(walltime,[W1,_]),    % wall time  
  ( entails(ABAF,Ep0,En0,[E],[]) -> Res=yes ; Res=no ),
  statistics(runtime,[T2,_]),     T is T2-T1,   
  statistics(system_time,[S2,_]), S is S2-S1,
  statistics(walltime,[W2,_]),    W is W2-W1,
  write(W), write(','), Lt is T+S, write(Lt), write(',').

%
ex_rules(ABAF,F, ABAFwER) :-
  ex_rules_aux(F,R),
  aba_ni_rules_append(ABAF,R, ABAF1),
  consts_in_BK(R,[], Cs), 
  findall(dr(dom(C)), member(C,Cs), DRs),
  utl_rules_append(ABAF1,DRs, ABAFwER).

%
ex_rules_aux([],[]).
ex_rules_aux([F|Fs],[R|Rs]) :-
  new_rule(F,[], R),
  ex_rules_aux(Fs,Rs).