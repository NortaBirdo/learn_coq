Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  rewrite -> H1.
  intros H2.
  rewrite -> H2.
  reflexivity.
Qed.