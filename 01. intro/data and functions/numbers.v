Module NatPlayground.
(*unary numbers. 2 is  S (S O)*)
  Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Check (S (S (S (S O)))).

Check 10.
(* ===> 4 : nat *)
Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n' (* if n has the form S n' for some n', then return n' *)
  end.
Compute (minustwo 4).
(* ===> 2 : nat *)

(* ================================== *)
Fixpoint even (n:nat) : bool :=
  (* Fixpoint - recursion*)
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.



Definition odd (n:nat) : bool :=
  negb (even n).
Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.