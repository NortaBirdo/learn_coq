Theorem andb_true_elim2 : 
  forall b c : bool,
  andb b c = true -> c = true.
Proof.
    intros [] [].
    reflexivity.
    simpl.
    (* the second goal with contradiction*)
    intros H1.
    rewrite <- H1.
    reflexivity.
    (*the third goal*)
    simpl.
    intros H2.
    rewrite <- H2.
    reflexivity.
    (*fourth goal*)
    simpl.
    intros H3.
    rewrite <- H3.
    reflexivity.
Qed.

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

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
    intros [| n'].
    reflexivity.
    reflexivity.
Qed.
