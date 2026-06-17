:- use_module(library(csv)).

pm :-  
  write('acute'),    nl, load_csv('xabal/acute',[grd,stb,adm,com,prf]),   nl,
  write('autism'),   nl, load_csv('xabal/autism',[grd,stb,adm,com,prf]),  nl,
  write('breastw'),  nl, load_csv('xabal/breastw',[grd,stb,adm,com,prf]), nl,
  write('krkp'),     nl, load_csv('xabal/krkp',[grd,stb,adm,com,prf]),    nl,
  write('mushroom'), nl, load_csv('xabal/mushroom',[grd,stb,adm,com,prf]),nl,
  write('voting'),   nl, load_csv('xabal/voting',[grd,stb,adm,com,prf]),  nl,
  halt.

%
load_csv(_,[]).
load_csv(File,[S|Ss]) :-
  atom_concat(File,'.',Tmp), atom_concat(Tmp,S,Tmp1), atom_concat(Tmp1,'.PM.csv',FilePM),
  tell(FilePM),
  write('ID,tot,P,N,TP,TN,FP,FN,Accuracy,Precision,Recall,F1'), nl,
  load_csv_aux(File,S,1, 6),
  told,
  load_csv(File,Ss).

%
load_csv_aux(_,_,N,N).
load_csv_aux(File,S,I, O) :-
  load_csv_loop(File,I,S),
  I1 is I+1,
  load_csv_aux(File,S,I1, O).

%
load_csv_loop(FileBaseName,I,S) :-
  atom_concat(FileBaseName,'.csv.f',Tmp1), 
  atom_number(A,I), atom_concat(Tmp1,A,Tmp2),
  atom_concat(Tmp2,'.bk.sol.',Tmp3),
  atom_concat(Tmp3,S,Tmp4), 
  atom_concat(Tmp4,'.test.csv',File),
  write('f'), write(A), write(','),
  load_csv_tail(File).

%
load_csv_tail(File) :-
  exists_file(File),
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
load_csv_tail(_) :-
  write('to'), nl. 

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