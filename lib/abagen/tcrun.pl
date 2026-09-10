:- use_module(library(csv)).

:- consult('../../xabal.pl').

tcrun_csv(File) :-
  csv_read_file(File,[_|Rows],[functor(tc)]),
  tcrun_csv_aux(Rows).
%
tcrun_csv_aux([]).
tcrun_csv_aux([TC|TCs]) :-
  arg(1,TC,TCFile),
  tcrun(TCFile),
  tcrun_csv_aux(TCs).  


tcrun(TC) :-
  consult(TC),
  findall(Name,bk(Name),BKs),
  learn_and_test_ABAFs(BKs),
  retractall(bk(_)),
  retractall(lp(_)),
  retractall(fold(_,_,_,_,_)).

%
learn_and_test_ABAFs([]).
learn_and_test_ABAFs([BK|BKs]) :-
  %learn_and_test(BK),
  performance_eval(BK),
  learn_and_test_ABAFs(BKs).

%
learn_and_test(BK) :-
  learn_and_test_5fCV(BK,1).

%
learn_and_test_5fCV(_,6).
learn_and_test_5fCV(BK,I) :-
  I =< 5,
  fold(I,LearningEp,LearningEn,TestingEp,TestingEn),
  lp(Lp),
  % run X-ABALearn on <LearningEp,LearningEn>
  xabal(BK,LearningEp,LearningEn,Lp),
  atom_concat(BaseFileName,'.aba',BK),
  atom_concat(BaseFileName,'.sol.aba',SolName),
  ( exists_file(SolName) ->
    (
      atomic_list_concat([BaseFileName,'.f',I,'.sol.aba'],NewSolName),
      rename_file(SolName,NewSolName),
      % test entailment of <TestingEp,TestingEn>
      test_abaf(NewSolName,TestingEp,TestingEn)
    )
  ;
    true
  ),
  !,
  I1 is I+1,
  learn_and_test_5fCV(BK,I1).

%
performance_eval(BK) :-
  atom_concat(BaseFileName,'.aba',BK),
  atom_concat(BaseFileName,'.PM.csv',FilePM),
  tell(FilePM),
  write('ID,tot,P,N,TP,TN,FP,FN,Accuracy,Precision,Recall,F1'), nl,
  load_csv_aux(BaseFileName,1),
  told,
  append_performance_res(BaseFileName,FilePM).

%
load_csv_aux(_,6).
load_csv_aux(File,I) :-
  I < 6, 
  load_csv_loop(File,I),
  I1 is I+1,
  load_csv_aux(File,I1).

%
load_csv_loop(FileBaseName,I) :-
  atomic_list_concat([FileBaseName,'.f',I,'.sol.test.csv'],File),
  exists_file(File),
  !,
  write('f'), write(I), write(','),
  csv_read_file(File,Rows,[functor(d)]),
  length(Rows,L), write(L), write(','), % total num of elements
  compute_metrics(Rows,0,0,0,0,0,0, P,N,TP,TN,FP,FN),
  write(P),  write(','), 
  write(N),  write(','),
  write(TP), write(','), 
  write(TN), write(','),
  write(FP), write(','), 
  write(FN), write(','),
  accuracy(P,N,TP,TN, Aval), format('~2f',Aval),  write(','), 
  precision(TP,FP,    Pval), format('~2f',Pval),  write(','), 
  recall(TP,FN,       Rval), format('~2f',Rval),  write(','),
  f1score(TP,FP,FN,  F1val), format('~2f',F1val), nl.
load_csv_loop(_FileBaseName,_I).

%
compute_metrics([],P_in,N_in,TP_in,TN_in,FP_in,FN_in, P_in,N_in,TP_in,TN_in,FP_in,FN_in).
compute_metrics([Row|Rows],P_in,N_in,TP_in,TN_in,FP_in,FN_in, P_out,N_out,TP_out,TN_out,FP_out,FN_out) :-
  Row = d(_,Sign,_,_,Res),
  compute_metrics_aux(Sign,Res, P_in,N_in,TP_in,TN_in,FP_in,FN_in, P_in1,N_in1,TP_in1,TN_in1,FP_in1,FN_in1),
  compute_metrics(Rows,P_in1,N_in1,TP_in1,TN_in1,FP_in1,FN_in1, P_out,N_out,TP_out,TN_out,FP_out,FN_out).

%
compute_metrics_aux(
   pos,yes, 
   P_in, N_in,TP_in, TN_in,FP_in,FN_in, 
   P_in1,N_in,TP_in1,TN_in,FP_in,FN_in) :-
   P_in1 is P_in + 1,
   TP_in1 is TP_in + 1.
compute_metrics_aux(
   pos,no, 
   P_in, N_in,TP_in,TN_in,FP_in,FN_in, 
   P_in1,N_in,TP_in,TN_in,FP_in,FN_in1) :-
   P_in1 is P_in + 1,
   FN_in1 is FN_in + 1.
compute_metrics_aux(
   neg,yes, 
   P_in,N_in, TP_in,TN_in,FP_in,FN_in, 
   P_in,N_in1,TP_in,TN_in,FP_in1,FN_in) :-
   N_in1 is N_in + 1,
   FP_in1 is FP_in + 1.
compute_metrics_aux(
   neg,no, 
   P_in,N_in, TP_in,TN_in,FP_in,FN_in, 
   P_in,N_in1,TP_in,TN_in1,FP_in,FN_in) :-
   N_in1 is N_in + 1,
   TN_in1 is TN_in + 1.

%
accuracy(P,N,TP,TN, A) :-
  Num is TP+TN,
  ( Num == 0 ->
    A = 0
  ;
    ( Den is P+N, A is Num/Den )
  ).
%
precision(TP,_FP, P) :-
  TP == 0,
  !,
  P = 0.  
precision(TP,FP, P) :-
  Den is TP+FP,
  P is TP/Den.
%
recall(TP,_FN, R) :-
  TP == 0,
  !,
  R = 0.  
recall(TP,FN, R) :-
  Den is TP+FN,
  R is TP/Den.  
%
f1score(TP,_FP,_FN, F1) :-
  TP == 0,
  !,
  F1 = 0.
f1score(TP,FP,FN, F1) :-
  Num is 2*TP,
  Den is Num + FP+FN,
  F1 is Num/Den. 

%
append_performance_res(ABAFile,File) :-
  csv_read_file(File,[_|Rows],[functor(d)]),
  length(Rows,N),
  N > 0,
  !,
  averages(Rows,0,0,0,0, AcA,PrA,ReA,F1A),
  % Check if the file does not exist or is empty (size 0)
  ( ( \+ exists_file('PM.csv') ; size_file('PM.csv', 0) ) ->
    NeedsHeader = true
  ;   
    NeedsHeader = false
  ),
  atomic_list_concat([_,ID,Type],'.',ABAFile),
  setup_call_cleanup(
      open('PM.csv', append, Out),
        (
          ( NeedsHeader == true ->
          % write header row
          csv_write_stream(Out, [row('TestCase','ID','Type','Accuracy','Precision','Recall','F1')], [])
          ;   
            true
          ), 
        % write data row
        csv_write_stream(Out, [row(ABAFile,ID,Type,AcA,PrA,ReA,F1A)], []) 
        ),
      close(Out)
  ).
append_performance_res(_ABAFile,_File).  
%
averages([],AcI,PrI,ReI,F1I, AcA,PrA,ReA,F1A) :-
  AcA is AcI / 5,
  PrA is PrI / 5,
  ReA is ReI / 5,
  F1A is F1I / 5.
averages([Row|Rows],AcI,PrI,ReI,F1I, AcA,PrA,ReA,F1A) :-
  arg( 9,Row,Ac),
  arg(10,Row,Pr),
  arg(11,Row,Re),
  arg(12,Row,F1),
  AcI1 is AcI+Ac,
  PrI1 is PrI+Pr,
  ReI1 is ReI+Re,
  F1I1 is F1I+F1,
  averages(Rows,AcI1,PrI1,ReI1,F1I1, AcA,PrA,ReA,F1A).