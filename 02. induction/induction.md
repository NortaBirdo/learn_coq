# Induction 

the _principle of induction_ over natural numbers...
 - If [P(n)] is some proposition involving a natural number [n],
    and we want to show that [P] holds for _all_ numbers, we can reason like this:
    - show that [P(O)] holds
    - show that, if [P(n')] holds, then so does [P(S n')]
    - conclude that [P(n)] holds for all [n].

The syntax:

`induction n as [| n' IHn'].` where `IHn'` is a name of induction hypothesis.

The approach:

<pre>
Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.
</pre>

To define which variable should be under induction you need to revise Definition. The variable which is used in match must be used for an induction.

**The shape of a proof by induction will match the recursive structure of the program being verified, so make the recursions as simple as possible.**

# Proofs inside proof

## Using of  Lemma

Suppose we are proving some theorem:

<pre>
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros n m.
  induction m as [|m' IHm'].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite <- IHm'. 
</pre>

At this point we need a proved statement `S (n + m) = n + (S m).` but we don't want to look aside  now. So, we can use `Admitted` in the way:

<pre>
Lemma plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof. Admitted.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros n m.
  induction m as [|m' IHm'].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite <- IHm'. rewrite plus_n_Sm. reflexivity.
Qed.
</pre>

## `assert` tactic

Sometimes it's more convenient the small proofs to include inside the big one. `assert` does it.

<pre>
Theorem mult_0_plus : forall n m : nat,
 (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert ( H : n + 0 + 0 = n).
   { rewrite add_comm. simpl. rewrite add_comm. reflexivity.}
  rewrite -> H.
  reflexivity.
Qed.
</pre>

`Set Printing Parentheses` - makes Coq add parentheses explicitly in a goal printing.