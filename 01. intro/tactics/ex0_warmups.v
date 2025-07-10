Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f.
  intros H1.
  intros H2.
  rewrite <- H1.
  rewrite -> H1.
  reflexivity.
Qed.
   

(* Prove the following theorem.*)
Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c.
  destruct b eqn:Eb.
  simpl.
  intros H1.
  rewrite -> H1.
  reflexivity.
  (*second case*)
  simpl.
  intros H2.
  rewrite -> H2.
  reflexivity.
Qed.
