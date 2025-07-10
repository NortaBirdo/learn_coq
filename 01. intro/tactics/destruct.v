Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem plus_1_neg_0_firsttry : 
  forall n : nat,
  (n + 1) =? 0 = false.
Proof.
    intros n.
    simpl.
Abort.