% grounded semantics
n_assumptions(N) :- #count{X : assumption(X)} = N.
iteration(0..N-1) :- n_assumptions(N).
in(X,I) :- iteration(J), assumption(X), not attacked_by_undefeated(X,J), J+1=I.
supported(X,I) :- assumption(X), in(X,I).
supported(X,I) :- head(R,X), triggered_by_in(R,I).
triggered_by_in(R,I) :- iteration(I), head(R,_), supported(X,I) : body(R,X).
defeated(X,I) :- supported(Y,I), contrary(X,Y).
derived_from_undefeated(X,I) :- iteration(I), assumption(X), not defeated(X,I).
derived_from_undefeated(X,I) :- head(R,X), triggered_by_undefeated(R,I).
triggered_by_undefeated(R,I) :- iteration(I), head(R,_), derived_from_undefeated(X,I) : body(R,X).
attacked_by_undefeated(X,I) :- contrary(X,Y), derived_from_undefeated(Y,I).

% ABALearn utility predicate
supported(X) :- n_assumptions(N), I<=N, supported(X,I).
%supported(X) :- supported(X,I).

% bogus assumption
assumption(bogus).
contrary(bogus, c_bogus). 
head(id(0),c_bogus).