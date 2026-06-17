% pi_common
in(X) :- assumption(X), not out(X).
out(X) :- assumption(X), not in(X).
supported(X) :- assumption(X), in(X).
supported(X) :- head(R,X), supported(Y) : body(R,Y).
defeated(X) :- supported(Y), contrary(X,Y).
:- in(X), defeated(X). % conflict-free

% --------------------------------------------------
% admissible semantics
derived_from_undefeated(X) :- assumption(X), not defeated(X).
derived_from_undefeated(X) :- head(R,X), triggered_by_undefeated(R).
triggered_by_undefeated(R) :- head(R,_), derived_from_undefeated(X) : body(R,X).
attacked_by_undefeated(X) :- contrary(X,Y), derived_from_undefeated(Y).
:- in(X), attacked_by_undefeated(X).

% bogus assumption
assumption(bogus).
contrary(bogus, c_bogus). 
head(id(0),c_bogus).