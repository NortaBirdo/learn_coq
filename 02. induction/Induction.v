From LF Require Export Basics.

(*Print LoadPath.*)

(*
SUMMARY OF PROVED THEOREMS 

add_0_l : forall n : nat, 0 + n = n.
add_0_r : forall n:nat, n + 0 = n.
minus_n_n : forall n, n - n = 0.
double_plus : forall n, double n = n + n .
add_comm : forall n m : nat, n + m = m + n.
add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).

mul_0_r : forall n:nat, n * 0 = 0.
mult_1_l : forall n:nat, 1 * n = n.
mul_comm : forall m n : nat, m * n = n * m.
mult_assoc : forall n m p : nat, n * (m * p) = (n * m) * p.
mult_plus_distr_r : forall n m p : nat, (n + m) * p = (n * p) + (m * p).

eqb_refl : forall n : nat, (n =? n) = true.
double_eq : forall b : bool , negb ( negb b ) = b.
even_S : forall n : nat, even (S n) = negb (even n).
leb_refl : forall n:nat, (n <=? n) = true.
zero_neqb_S : forall n:nat, 0 =? (S n) = false.
andb_false_r : forall b : bool, andb b false = false.
S_neqb_0 : forall n:nat, (S n) =? 0 = false.
all3_spec : forall b c : bool, orb (andb b c) (orb (negb b) (negb c)) = true.

nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
double_bin_to_nat : forall b : bin, bin_to_nat b + bin_to_nat b = double (bin_to_nat(b)).
bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
nat_to_bin_double : forall m , nat_to_bin (m + m) = double_bin (nat_to_bin m).

double_incr : forall n : nat, double (S n) = S (S (double n))
double_incr_bin : forall b, double_bin (incr b) = incr (incr (double_bin b)).
eq_incr : forall m : nat, incr (nat_to_bin m) = nat_to_bin (S m).

eq_double : forall b: bin, double_bin (nat_to_bin (bin_to_nat b)) = nat_to_bin( double(bin_to_nat b)).
bin_to_nat_pres_incr : forall b : bin, bin_to_nat (incr b)  = 1 + bin_to_nat b.

*)


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

(*Exercise: 3 stars, standard, especially useful (mul_comm)*)

Theorem add_shuffle3 : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite add_assoc. rewrite add_comm. rewrite add_assoc. rewrite add_comm.
  assert ( H : n+p = p+n).
  {rewrite add_comm. reflexivity. }
  rewrite H. reflexivity.
Qed.

Check mult_n_Sm.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros m n.
  Set Printing Parenthese.
  induction m as [|m' IHm'].
  - rewrite mul_0_r. reflexivity.
  - simpl. rewrite add_comm. rewrite IHm'. rewrite <- mult_n_Sm. reflexivity.
Qed.

(*Exercise: 2 stars, standard, optional (plus_leb_compat_l*)
Check leb.

Theorem plus_leb_compat_l : forall n m p : nat,
  n <=? m = true -> (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.

  induction p as [| p' IHp'].
  - simpl. rewrite H. reflexivity.
  - simpl. rewrite IHp'. reflexivity.
Qed.

(*Exercise: 3 stars, standard, optional (more_exercises)

(a) it can be proved using only simplification and rewriting, 
(b) it also requires case analysis (destruct), or 
(c) it also requires induction.
*)
Theorem leb_refl : forall n:nat,
  (n <=? n) = true.
Proof.
 (*guessing: a, truely c*)
 intros n. induction n as [|n'].
 - reflexivity.
 - simpl. rewrite IHn'. reflexivity.
Qed.


Theorem zero_neqb_S : forall n:nat,
  0 =? (S n) = false.
Proof.
 (*gussing c*)
 intros n. induction n as [| n'].
 - reflexivity.
 - simpl. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
 (*guessing b*)
  intros b. destruct b.
  - reflexivity.
  - reflexivity.
Qed.

Theorem S_neqb_0 : forall n:nat,
  (S n) =? 0 = false.
Proof.
 (*guessing a*)
 intros n.
 reflexivity.
Qed.
 
Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  (*guessing b*)
  intros n. destruct n as [| n'].
  - reflexivity.
  - simpl. rewrite plus_n_Sm. rewrite add_comm. rewrite plus_1_l. reflexivity.
Qed. 


Theorem all3_spec : forall b c : bool,
  orb
    (andb b c)
    (orb (negb b)
         (negb c))
  = true.
Proof.
  (*guessing b*)
  intros b c. destruct b, c.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.
  
Check mult_n_Sm.
(*
mult_n_Sm
     : forall n m : nat, n * m + n = n * S m

*)

Set Printing Parentheses.
Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  (*guessing c*)
  induction p as [| p'].
  - rewrite mult_n_0_m_0. rewrite mul_0_r. reflexivity.
  - rewrite <- mult_n_Sm. 
    rewrite <-mult_n_Sm. 
    rewrite <- mult_n_Sm. (*remove S p *)
    Set Printing Parentheses. 
    rewrite (add_comm (n*p') n). 
    rewrite (add_comm (m * p') m). 
    rewrite (add_shuffle3 (n + (n * p')) m (m * p') ).
    rewrite (add_comm (n + (n * p')) (m * p')).
    rewrite (add_comm n (n * p')).
    rewrite (add_shuffle3 m (m * p') ((n * p') + n) ).
    rewrite (add_shuffle3 m (n * p') n).
    (*  (((n + m) * p') + (n + m)) = ((m * p') + ((n * p') + (m + n)))   *)
    rewrite (add_assoc (m * p') (n * p') (m + n)).
    rewrite (add_comm (m * p') (n * p')).
    rewrite (add_comm m n).
    rewrite IHp'.
    reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  (*guessing c*)
  intros n m p. 
  induction p as [| p'].
  - Set Printing Parentheses. rewrite mul_0_r. rewrite mul_0_r. rewrite mul_0_r. reflexivity.
  - Set Printing Parentheses. (*  (n * (m * (S p'))) = ((n * m) * (S p'))  *)
    rewrite <- mult_n_Sm.
    rewrite <- mult_n_Sm. Set Printing Parentheses. (* (n * ((m * p') + m)) = (((n * m) * p') + (n * m))  *)
    rewrite add_comm.
    rewrite mul_comm.
    rewrite mult_plus_distr_r. 
    rewrite (mul_comm (m * p') n).
    rewrite add_comm. 
    rewrite IHp'.
    rewrite (mul_comm m n).
    reflexivity.
Qed.

(*Exercise: 2 stars, standard, optional (add_shuffle3')

The replace tactic allows you to specify a particular subterm to 
rewrite and what you want it rewritten to: replace (t) with (u) replaces 
(all copies of) expression t in the goal by expression u, 
and generates t = u as an additional subgoal.

*)

Theorem add_shuffle3' : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
 intros n m p. Set Printing Parentheses. (*  (n + (m + p)) = (m + (n + p))  *)
 induction n as [| n'].
 - simpl. reflexivity.
 - Set Printing Parentheses.
  (*  ((S n') + (m + p)) = (m + ((S n') + p))  *)
  replace (m + p) with (p + m).
  rewrite add_assoc. Set Printing Parentheses.
  (*  (((S n') + p) + m) = (m + ((S n') + p))  *)
  rewrite (add_comm ((S n') + p) m).
  reflexivity.
  (*proof p + m = m + p *)
  rewrite add_comm. reflexivity.
Qed.

(*

Theorem add_comm : forall n m : nat,
  n + m = m + n.

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.

mult_n_Sm: forall n m : nat, 
  n * m + n = n * S m *)


(*=================Nat to Bin and Back to Nat==================*)

Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).

Fixpoint incr (m:bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n' => B1 n'
  | B1 n' => B0 (incr n')
  end.

Fixpoint bin_to_nat (m:bin) : nat :=
  match m with
  | Z => O
  | B1 Z => S O
  | B0 n' => mult 2 (bin_to_nat n')
  | B1 n' => plus 1 (mult 2 (bin_to_nat n'))
  end.

(*Exercise: 3 stars, standard, especially useful (binary_commute)*)

Theorem bin_to_nat_pres_incr : forall b : bin, 
  bin_to_nat (incr b)  = 1 + bin_to_nat b.
Proof.
  intros b. induction b as [Z | B0 | B1].
  - simpl. reflexivity.
  - simpl. rewrite add_0_r. destruct B0.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. reflexivity.
 - simpl. rewrite add_0_r. destruct B1.
   + reflexivity.
   + rewrite add_0_r. rewrite IHB1. Set Printing Parentheses. 
   (*((1 + (bin_to_nat (B0 B2))) + (1 + (bin_to_nat (B0 B2)))) = (S (S ((bin_to_nat (B0 B2)) + (bin_to_nat (B0 B2)))))*)
   rewrite add_assoc. Set Printing Parentheses. 
   (*(((1 + (bin_to_nat (B0 B2)) + 1) + (bin_to_nat (B0 B2))) = (S (S ((bin_to_nat (B0 B2)) + (bin_to_nat (B0 B2)))))*)
   rewrite <- (add_comm (bin_to_nat (B0 B2)) 1). Set Printing Parentheses. 
   (*((((bin_to_nat (B0 B2)) + 1) + 1) + (bin_to_nat (B0 B2))) = (S (S ((bin_to_nat (B0 B2)) + (bin_to_nat (B0 B2)))))*)
   rewrite <- (add_assoc(bin_to_nat (B0 B2)) 1 1 ). rewrite (add_comm (bin_to_nat (B0 B2)) (1 + 1) ). Set Printing Parentheses. 
   (*(((1 + 1) + (bin_to_nat (B0 B2))) + (bin_to_nat (B0 B2))) = (S (S ((bin_to_nat (B0 B2)) + (bin_to_nat (B0 B2)))))*)
   reflexivity.
  + rewrite add_0_r. destruct B2. 
    * reflexivity.
    * rewrite IHB1. rewrite add_assoc. Set Printing Parentheses. 
      (* (((1 + (bin_to_nat (B1 (B0 B2)))) + 1) + (bin_to_nat (B1 (B0 B2)))) =
         (S (S ((bin_to_nat (B1 (B0 B2))) + (bin_to_nat (B1 (B0 B2))))))  *)
      rewrite (add_comm 1 (bin_to_nat (B1 (B0 B2)))). 
      rewrite <- (add_assoc (bin_to_nat (B1 (B0 B2))) 1 1).
      rewrite (add_comm (bin_to_nat (B1 (B0 B2))) (1 + 1)).
      reflexivity.
    * rewrite IHB1. rewrite add_assoc.
      rewrite (add_comm 1 (bin_to_nat (B1 (B1 B2)))).
      rewrite <- (add_assoc (bin_to_nat (B1 (B1 B2))) 1 1).
      rewrite (add_comm (bin_to_nat (B1 (B1 B2))) (1 + 1)).
      reflexivity.
Qed.
 


(*Exercise: 3 stars, standard (nat_bin_nat)
Write a function to convert natural numbers to binary numbers.
*)

(*
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Example test_bin_incr6 : bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
*)


Fixpoint nat_to_bin (n : nat) : bin :=
  match n with
  | O => Z
  | S O => incr (Z)
  | S n' => incr (nat_to_bin n')
end.

Example test_zero : nat_to_bin O = Z.
Proof. reflexivity. Qed.

Example test_one : nat_to_bin (S 0) = B1 Z.
Proof. reflexivity. Qed.

Example test_two : nat_to_bin (S (S O)) = B0 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_tree : nat_to_bin (S (S (S O))) = B1 (B1 Z).
Proof. simpl. reflexivity. Qed.

Example test_four : nat_to_bin 4 = B0 (B0 (B1 Z)).
Proof. simpl. reflexivity. Qed.



Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n'].
  - reflexivity. (*for n = 0*)
  - simpl. destruct n'. (*Here cases for n=1 and n + inf.*)
    + reflexivity. (*for n = 1*)
    + rewrite <- plus_1_l.
      rewrite bin_to_nat_pres_incr. 
      rewrite plus_n_Sm. 
      replace (1 + n') with (S n'). (*coq stub, adhoc*)
      * rewrite IHn'. reflexivity.
      * reflexivity.
Qed.



(*=============Bin to Nat and Back to Bin (Advanced)=============*)


(*Exercise: 2 stars, advanced (double_bin)*)

Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof. 
 intros n. simpl. reflexivity. Qed.

Definition double_bin (b:bin) : bin := 
 match b with
 | Z => Z
 | _ => B0 b
end.

Example double_bin_zero : double_bin Z = Z.
Proof. simpl. reflexivity. Qed.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
 intros b. destruct b.
 - reflexivity.
 - reflexivity.
 - reflexivity.
Qed.


(* Here is a problem with Z => BO BO Z. That's is equalent, 
but converting to nat will encourage trubles.*)


(*Do not use bin_to_nat or nat_to_bin, but do use double_bin. 
Keep its definition as simple as possible for later proofs to go smoothly. *)

(*The function reduce B0*)

(* This implementation is correct, but I can't prove the following theorem, 
since it doesn't use incr function. 

Fixpoint normalize (b:bin) : bin := 
 match b with
 | Z => Z
 | B0 Z => Z
 | B1 Z => B1 Z
 | B1 b' => B1 b'
 | B0 b' => double_bin (normalize b')
end.
*)

Fixpoint normalize (b : bin) : bin := 
 match b with
 | Z => Z
 | B1 b' => incr (double_bin (normalize b'))
 | B0 b' => double_bin ( normalize b' )
end.

Example positive_test_zero : normalize (Z) = Z. 
Proof. simpl. reflexivity. Qed.

Example positive_test_zero_to_norm : normalize (B0 Z) = Z. 
Proof. simpl. reflexivity. Qed.

Example positive_test_zero_norm_2 : normalize (B0 (B0 Z)) = Z. 
Proof. simpl. reflexivity. Qed.

Example negative_test_non_zero : normalize (B1 Z) = (B1 Z).
Proof. simpl. reflexivity. Qed. 

Example negative_test_non_zero_2 : 
 normalize ( B0 (B1 (B0 (B1 Z)))) = ( B0 (B1 (B0 (B1 Z)))).
Proof. simpl. reflexivity. Qed.

Example normalize_B0_Z: normalize (B0 Z) = Z.
Proof. simpl. reflexivity. Qed.

Lemma nat_to_bin_double : forall m , nat_to_bin (m + m) = double_bin (nat_to_bin m).
Proof. 
 intros m. induction m.
 - simpl. reflexivity.
 - simpl. rewrite <- plus_1_l. destruct m.
   + simpl. reflexivity.
   + rewrite double_incr_bin. rewrite <- IHm. 
     rewrite (add_comm 1 (S m)). rewrite (add_assoc (S m) (S m) 1). 
     rewrite <- double_plus. rewrite double_incr. 
     rewrite <- plus_n_Sm.  rewrite add_0_r. simpl. reflexivity.
Qed.

Lemma double_bin_to_nat : forall b : bin,
bin_to_nat b + bin_to_nat b = double (bin_to_nat(b)).
Proof. 
 intros b. induction b.
 - simpl. reflexivity.
 - simpl. rewrite add_0_r. rewrite IHb. rewrite <- double_plus. reflexivity.
 - simpl. rewrite add_0_r. rewrite <- double_plus. reflexivity.
Qed.


Lemma eq_double : forall b: bin, 
double_bin (nat_to_bin (bin_to_nat b)) = nat_to_bin( double(bin_to_nat b)).
Proof. 
 intros b. induction b.
 - simpl. reflexivity.
 - simpl. rewrite add_0_r. rewrite double_bin_to_nat.
   simpl.

Set Printing Parentheses.

 
Lemma eq_incr : forall m : nat,
  incr (nat_to_bin m) = nat_to_bin (S m).
Proof. 
 intros m. induction m.
 - simpl. reflexivity.
 - simpl. destruct m.
   +  simpl. reflexivity.
   +  reflexivity.
Qed.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof. 
 intros b. induction b. 
 - simpl. reflexivity. (*Z- case*)
 - simpl. destruct b. (*B0 _ case*)
   + simpl. reflexivity.
   + rewrite <- IHb. simpl. rewrite add_0_r. (*remove normalize and B0*)
     rewrite add_assoc. rewrite add_0_r. (*reduce zero*)
     rewrite nat_to_bin_double. reflexivity.
   + rewrite <- IHb. (*remove normalize and B0*)
     rewrite add_assoc. rewrite add_0_r. (*reduce zero*)
     rewrite nat_to_bin_double. reflexivity.
 - simpl. rewrite <- IHb. 
   rewrite add_assoc. rewrite add_0_r. rewrite IHb.
   rewrite double_bin_to_nat. destruct b.
   + simpl. reflexivity.
   + rewrite <- IHb. rewrite eq_double. rewrite eq_incr. reflexivity.
   + rewrite <- IHb. rewrite eq_double. rewrite eq_incr. reflexivity.
Qed.

