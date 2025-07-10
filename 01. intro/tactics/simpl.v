(*the simplest example*)

Theorem plus_1_l : 
  forall n:nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.