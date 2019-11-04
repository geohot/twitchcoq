# twitchcoq -- a backspace.ai project

Reimplementing a subset of Coq in Python. 

Just kidding, Coq is too complex. We implemented metamath instead.

It (slowly) verifies set.mm as of 11/3/2019

Ideally, Coq and friends should be rewritten in metamath. It's really the future, just wish it looked better. But omg, this is the proper stack for formal math, "formalism" is alive and well and is the truth in philosophy.

# metamath as execution

We should be able to "run" a metamath program, aka proof without the target. It's a stack machine.

# metamath on search

Take set.mm, remove all $p definitions. Find them with search. Powered by AI(tm).

"metasmash" written in C++17. First with the intermediate nodes in the graph. Then make it sparser. Then remove it altogether.

How many of the 71 Metamath theorems can we rediscover without the scaffolding?

Hmm, https://github.com/dwhalen/holophrasm

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

# randomer notes

Imagine twitch, but VR. We'll rebuild the cybercafes, the revolutionary coffee shops, the old hacker spaces, the town square, the churches, all of the trappings of civilization. But we'll build them in machines. We'll build them in math. We'll build them in homomorphically encrypted lockers. We'll build them where copies are free, tax is ridiculous, removing your landlord is a fork, and the only axis on which to compete is quality. True freedom of association.

We need embodiment to be free from the tyranny of owned space. And we need formalization to be secure.

The attacker vs defender battle may have been lost IRL. But in the world of information, the defender seems to win.

