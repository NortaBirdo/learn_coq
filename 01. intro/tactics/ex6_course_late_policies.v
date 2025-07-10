Module LateDays.
   Inductive letter : Type :=
  | A | B | C | D | F. 

  Inductive modifier : Type :=
  | Plus | Natural | Minus.

  Inductive grade : Type :=
  Grade (l:letter) (m:modifier).


  Inductive comparison : Type :=
  | Eq (* "equal" *)
  | Lt (* "less than" *)
  | Gt. (* "greater than" *)

Definition letter_comparison (l1 l2 : letter) : comparison :=
  match l1, l2 with
  | A, A => Eq
  | A, _ => Gt
  | B, A => Lt
  | B, B => Eq
  | B, _ => Gt
  | C, (A | B) => Lt
  | C, C => Eq
  | C, _ => Gt
  | D, (A | B | C) => Lt
  | D, D => Eq
  | D, _ => Gt
  | F, (A | B | C | D) => Lt
  | F, F => Eq
  end.

Compute letter_comparison B A.
Compute letter_comparison D D.
Compute letter_comparison B F.


(*Exercise: 1 star*)
Theorem letter_comparison_Eq :
  forall l, letter_comparison l l = Eq.
Proof.
    intros [].
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
Qed.
(*========================*)

Definition modifier_comparison (m1 m2 : modifier) : comparison :=
  match m1, m2 with
  | Plus, Plus => Eq
  | Plus, _ => Gt
  | Natural, Plus => Lt
  | Natural, Natural => Eq
  | Natural, _ => Gt
  | Minus, (Plus | Natural) => Lt
  | Minus, Minus => Eq
  end.

(*Exercise: 2 star
Use pattern matching to complete the following definition.
This ordering on grades is sometimes called "lexicographic" 
ordering: we first compare the letters, and we only consider 
the modifiers in the case that the letters are equal. 
I.e. all grade variants of A are greater than all grade variants of B.

https://stackoverflow.com/questions/76185627/software-foundations-basics-exercise-how-do-i-access-letter-from-grade
*)

Definition grade_comparison (g1 g2 : grade) : comparison := 
  match g1, g2 with
  | Grade l1 m1, Grade l2 m2 => 
    match letter_comparison l1 l2 with
    | Eq => modifier_comparison m1 m2
    | Lt => Lt
    | Gt => Gt
    end
  end.

Example test_grade_comparison1 :
  (grade_comparison (Grade A Minus) (Grade B Plus)) = Gt.
Proof. reflexivity. Qed. 

Example test_grade_comparison2 :
  (grade_comparison (Grade A Minus) (Grade A Plus)) = Lt.
Proof. reflexivity. Qed. 

Example test_grade_comparison3 :
  (grade_comparison (Grade F Plus) (Grade F Plus)) = Eq.
Proof. reflexivity. Qed. 

Example test_grade_comparison4 :
  (grade_comparison (Grade B Minus) (Grade C Plus)) = Gt. 
Proof. reflexivity. Qed. 

(*=====================*)

Definition lower_letter (l : letter) : letter :=
  match l with
  | A => B
  | B => C
  | C => D
  | D => F
  | F => F (* Can't go lower than F! *)
  end.

(*Exercise: 2 stars, standard (lower_letter_lowers)
Prove the following theorem.

Definition letter_comparison (l1 l2 : letter) : comparison :=
*)

Theorem lower_letter_lowers:
  forall (l : letter),
    letter_comparison F l = Lt ->
    letter_comparison (lower_letter l) l = Lt.
Proof.
    intros [].
    reflexivity.
    reflexivity.
    reflexivity.
    reflexivity.
    simpl.
    intros H1.
    rewrite -> H1.
    reflexivity.
Qed.

(*Exercise: 2 stars
Complete the definition below so that it sends 
a grade g to one step lower (unless it is already Grade F Minus, 
which should remain unchanged

Definition lower_letter (l : letter) : letter
*)
    
Definition lower_grade (g : grade) : grade :=
  match g with  
  | Grade F Minus => Grade F Minus
  | Grade F Natural => Grade F Minus
  | Grade F Plus => Grade F Natural
  | Grade l1 Minus => Grade (lower_letter(l1)) Plus
  | Grade l1 Plus => Grade l1 Natural
  | Grade l1 Natural => Grade l1 Minus
  end.

Example lower_grade_A_Plus :
  lower_grade (Grade A Plus) = (Grade A Natural).
Proof. reflexivity. Qed.

Example lower_grade_A_Natural :
  lower_grade (Grade A Natural) = (Grade A Minus).
Proof. reflexivity. Qed.

Example lower_grade_A_Minus :
  lower_grade (Grade A Minus) = (Grade B Plus).
Proof. reflexivity. Qed.

Example lower_grade_B_Plus :
  lower_grade (Grade B Plus) = (Grade B Natural).
Proof. reflexivity. Qed.

Example lower_grade_F_Natural :
  lower_grade (Grade F Natural) = (Grade F Minus).
Proof. reflexivity. Qed.

Example lower_grade_twice :
  lower_grade (lower_grade (Grade B Minus)) = (Grade C Natural).
Proof. reflexivity. Qed.

Example lower_grade_thrice :
  lower_grade (lower_grade (lower_grade (Grade B Minus))) = (Grade C Minus).
Proof. reflexivity. Qed.

Theorem lower_grade_F_Minus : lower_grade (Grade F Minus) = (Grade F Minus).
Proof. reflexivity. Qed.

(*Exercise: 3 stars
Prove the following theorem, which says that, 
as long as the grade starts out above F-,
the lower_grade option does indeed lower the grade*)

Check letter_comparison_Eq.


Theorem lower_grade_lowers :
  forall (g : grade),
    grade_comparison (Grade F Minus) g = Lt ->
    grade_comparison (lower_grade g) g = Lt.
Proof.
  intros g. 
  destruct g.
  destruct l eqn : El.
  + destruct m eqn : Em. 
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  + destruct m eqn : Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  + destruct m eqn : Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  + destruct m eqn : Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  + destruct m eqn : Em.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

(*==============*)

Fixpoint ltb (n m : nat) : bool :=
    match n, m with
    | O, O => false
    | O, S m' => true
    | S n', O => false
    | S n', S m' => ltb n' m'
    end.

    Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.


Definition apply_late_policy (late_days : nat) (g : grade) : grade :=
  if late_days <? 9 then g
  else if late_days <? 17 then lower_grade g
  else if late_days <? 21 then lower_grade (lower_grade g)
  else lower_grade (lower_grade (lower_grade g)).


Theorem apply_late_policy_unfold :
  forall (late_days : nat) (g : grade),
    (apply_late_policy late_days g)
    =
    (if late_days <? 9 then g else
       if late_days <? 17 then lower_grade g
       else if late_days <? 21 then lower_grade (lower_grade g)
            else lower_grade (lower_grade (lower_grade g))).
Proof.
  intros. reflexivity.
Qed.

(*Exercise: 2 stars*)
Theorem no_penalty_for_mostly_on_time :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = true) ->
    apply_late_policy late_days g = g.
Proof.
  intros late_days g.
  intros H.
  rewrite apply_late_policy_unfold.
  rewrite H.
  reflexivity.
Qed.

(*Exercise: 2 stars*)
Theorem grade_lowered_once :
  forall (late_days : nat) (g : grade),
    (late_days <? 9 = false) ->
    (late_days <? 17 = true) ->
    (apply_late_policy late_days g) = (lower_grade g).
Proof.
  intros late_days g.
  intros H1 H2.
  rewrite apply_late_policy_unfold.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.

End LateDays.