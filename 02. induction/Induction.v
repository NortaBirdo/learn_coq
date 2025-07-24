From LF Require Export Basics.

Example add_0_l : forall n : nat,
    0 + n = n.
Proof. reflexivity. Qed.


Theorem add_0_r_firsttry : forall n:nat,
  n + 0 = n.
(** ... gets stuck. *)
Proof.
  intros n.
  simpl. (* Does nothing! *)
Abort.

Theorem add_0_r_secondtry : forall n:nat,
  n + 0 = n.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    reflexivity. (* so far so good... *)
  - (* n = S n' *)
    simpl.       (* ...but here we are stuck again *)
Abort.

(** the _principle of induction_ over natural numbers...
      - If [P(n)] is some proposition involving a natural number [n],
        and we want to show that [P] holds for _all_ numbers, we can
        reason like this:
         - show that [P(O)] holds
         - show that, if [P(n')] holds, then so does [P(S n')]
         - conclude that [P(n)] holds for all [n].
\*)

Theorem add_0_r : forall n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)    reflexivity.
  - (* n = S n' *) simpl. rewrite -> IHn'. reflexivity.  Qed.

Theorem minus_n_n : forall n,
  n - n = 0.
Proof.
intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.


Theorem mul_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n.
  induction n as [| n].
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof. 
  intros n m.
  induction m as [|m' IHm'].
  - rewrite add_0_r. reflexivity.
  - simpl. rewrite <- IHm'. rewrite plus_n_Sm. reflexivity.
Qed.


Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.


Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
(*Use induction to prove this simple fact about double:*)

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.


Lemma double_eq : forall b : bool ,
  negb ( negb b ) = b.
Proof.
  intros b. destruct b.
  - simpl. reflexivity.
  - reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl. rewrite <- IHn'. destruct n'.
    + simpl. reflexivity.
    + rewrite IHn'. rewrite double_eq. reflexivity. 
   (* + rewrite IHn'. rewrite negb_involutive. reflexivity. *)
Qed.











