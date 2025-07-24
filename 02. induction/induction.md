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