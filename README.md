# twitchcoq

Reimplementing a subset of Coq in Python

Just kidding, Coq is too complex. We implemented metamath instead.

Ideally, Coq and friends should be rewritten in metamath. It's really the future, just wish it looked better. But omg, this is the proper stack for formal math, "formalism" is alive and well and is the truth in philosophy.

# metamath as execution

We should be able to "run" a metamath program, aka proof without the target. It's a stack machine.

# metamath on search

Take set.mm, remove all $p definitions. Find them with search. Powered by AI(tm)

# random notes

First order logic:

<pre>
Theorem test : exists x : nat, x + 2 = 4.
Theorem test2 : forall y : nat, (exists x : nat, x = y).
</pre>

Second order logic (quantifing over first order logic statements):

<pre>
forall y : (fun x : nat -> nat)
</pre>

Higher order logic...so on and so forth

