# Pair creation

List is analog of tuple in Python.

To use constractor `pair`
<pre>
Inductive natprod : Type := 
 | pair (n1 n2 : nat).
</pre>

## Pattern matching

<pre>
... p : natprod ...
...
match p with
| pair x y => ...
</pre>

## Theorem proving

The `simpl` and `reflexivity` can't look inside `p`. So for theorem proving you have to use `destruct p as [n m]` firstly, so Coq can union it.

# List