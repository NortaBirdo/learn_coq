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

<pre>
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
</pre>

`cons` - contractor of a list.

## list induction

Works the same as for a nat because the nat is a sequence too.

# options
Options represent a partial function in terms of math - a functions that is not defined by some inputs.

Suppose we want to write a function that returns the nth element of some list. If we give it type nat → natlist → nat, then we'll have to choose some number to return when the list is too short...

<pre>
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
</pre>

There are `some` and `none` constructors of Coq. They might be begin with either capital or lowercase letters.

# Partial Maps

This is a key-value data type. There are two ways to construct a partial_map: either using the constructor empty to represent an empty partial map, or applying the constructor record to a key, a value, and an existing partial_map to construct a partial_map with an additional key-to-value mapping.

<pre>
Inductive id : Type :=
  | Id (n : nat).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).

Definition update (d : partial_map)
                  (x : id) (value : nat)
                  : partial_map :=
  record x value d.
</pre>