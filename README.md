# X-ABALearn 

Starting SWI-Prolog

```
$ swipl
Welcome to SWI-Prolog (threaded, 64 bits, version 9.2.9)
SWI-Prolog comes with ABSOLUTELY NO WARRANTY. This is free software.
Please run ?- license. for legal details.

For online help and background, visit https://www.swi-prolog.org
For built-in help, use ?- help(Topic). or ?- apropos(Word).

?-
````

Loading X-ABALearn

```prolog
?- consult('xabal.pl').
```

`xabal.pl` provides the predicate `xabal(+BK,+Ep,+En,-S)` to compute solutions of an ABA learning problem; 
it holds if and only if `S` is (a Prolog term representing) a solution of the ABA learning problem specified as follow:
* `BK` is the file containing the encoding of the ABA framework representing the Background Knowledge (conventionally, `BK` must have the extension `.aba`),
* `Ep` is the list of positive examples, and
* `En` is the list of negative examples.

Any solution is printed to a file named `BK.sol.aba` (its ASP encoding is printed to a file named `BK.sol.asp`).

```prolog
xabal('./examples/flies_birds.bk',[flies(woodstock),flies(gwaihir),flies(x_pingu),flies(x_pinga)],[flies(pingu),flies(pinga)]).
```

The predicate `xabal(+BK,+Ep,+En)` can be used instead of `xabal(+BK,+Ep,+En,-S)` if the user is not interested in the Prolog term `S`. 

## Encoding the Background Knowledge

The Background Knowledge is an ABA framework including the following additional predicates:

* `assumption(A)` representing that `A` is an assumption
* `contrary(A,C)` representing that `C` is the contrary of `A`, and it is defined by a rule of the form 
`contrary(A,C) :- assumption(A).` 