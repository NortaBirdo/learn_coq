Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.

Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* moves the hypothesis n = m into the context and gives it the name H. *)
  intros H.
  (* tells Coq to rewrite the current goal (n + n = m + m) by replacing the left side of the equality 
  hypothesis H with the right side. 
  
  The direction of an arrow shows which part Coq should rewrite.
  In this case it is left.*)

  rewrite -> H.
  reflexivity. Qed.

  (*The arrow symbol in the rewrite has nothing to do with implication:
   it tells Coq to apply the rewrite from left to right. In fact, we can omit the arrow,
   and Coq will default to rewriting left to right. 
   To rewrite from right to left, use rewrite <-.*)