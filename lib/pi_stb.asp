% pi_common
in(X) :- assumption(X), not out(X).
out(X) :- assumption(X), not in(X).
supported(X) :- assumption(X), in(X).
supported(X) :- head(R,X), supported(Y) : body(R,Y).
defeated(X) :- supported(Y), contrary(X,Y).
:- in(X), defeated(X). % conflict-free

% --------------------------------------------------
% stable semantics
:- out(X), not defeated(X).

% bogus assumption
assumption(bogus).
contrary(bogus, c_bogus). 
head(id(0),c_bogus).