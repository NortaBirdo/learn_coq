From LF Require Export Poly.

(*========== APPLY ==============*)

Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. (*the shortcut for rewrite → eq. reflexivity. *)
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (n = m -> [n;o] = [m;p]) ->
  [n;o] = [m;p].
Proof.
 intros n m o p eq1 eq2.
 apply eq2. apply eq1. 
Qed.

Theorem silly2a : forall (n m : nat),
  (n, n) = (m, m) ->
  (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1. 
Qed.

(*Exercise: 2 stars, standard, optional (silly_ex)*)
Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
 intros.
 apply H0. apply H. apply H1.
Qed.


(*======SYMMETRY============*)
Theorem silly3 : forall (n m : nat),
  n = m ->
  m = n.
Proof.
  intros n m H.
  symmetry. apply H.
Qed.

(*Exercise: 2 stars, standard (apply_exercise1)*)
Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
 intros. 
 rewrite H. 
 symmetry.
 apply rev_involutive.
Qed.

(*Exercise: 1 star, standard, optional (apply_rewrite)
Briefly explain the difference between the tactics apply and rewrite. 
What are the situations where both can usefully be applied?

Apply does rewrite using hypotheses and reflexivity and the same time. This is a sugar.
Rewrite is more flexible and could be applied in case of lefthand rewritting or rewritting specific parts.
*)


(*===============APPLY WITH==============*)
Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. apply eq2.
Qed.


Theorem trans_eq : forall (X:Type) (x y z : X),
  x = y -> y = z -> x = z.
Proof.
  intros X x y z eq1 eq2. 
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity. 
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (y:=[c;d]). 
(*If we simply tell Coq apply trans_eq at this point, 
it can tell (by matching the goal against the conclusion of the lemma) 
that it should instantiate X with [nat], n with [a,b], and o with [e,f]. 
However, the matching process doesn't determine an instantiation for m: 
we have to supply one explicitly by adding "with (m:=[c,d])" to the invocation of apply.*)
  apply eq1. 
  apply eq2. 
Qed.



(*==============TRANSITIVITY============= *)

Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2.
Qed.

(*Exercise: 3 stars, standard, optional (trans_eq_exercise)*)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
 intros.
 transitivity m. 
 apply H0.
 apply H.
Qed.

(*===============INJECTION===============*)
Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  injection H as Hnm.
  apply Hnm.
Qed.

Theorem injection_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. symmetry. apply H2.
Qed.

(*Exercise: 3 stars, standard (injection_ex3)*)

Example injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
 intros. 
 (* we must show, that if x::y::l = z::z::l then x=z, y=z, so x=y *)
 injection H. rewrite H0. 
 (*firstly remove two arrows and ADD x = z*)
 transitivity x. reflexivity.
 (*now do the same for y = z*)
  rewrite H2. injection H1. intros. symmetry. apply H3.
Qed. 
 
(*=================DISCRIMINATE ==============*)

Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. 
Qed.

Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. discriminate contra. 
Qed.

(*Exercise: 1 star, standard (discriminate_ex3)*)
Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
 intros. discriminate H.
Qed. 

Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
 destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* S n = 0*) simpl. intros H. discriminate H.
Qed.


(*===============f_equal==============*)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof.
 intros A B f x y eq. 
 rewrite eq. reflexivity.
Qed.

Theorem eq_implies_succ_equal : forall (n m : nat),
  n = m -> S n = S m.
Proof. 
 intros n m H.
 apply f_equal.
 apply H.
Qed.

Theorem eq_implies_succ_equal' : forall (n m : nat),
  n = m -> S n = S m.
Proof.
 intros n m H. f_equal. apply H. 
Qed.

(*=============Using Tactics on Hypotheses=========*)
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H. 
  simpl in H. 
  apply H. 
Qed.

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.
Qed.


(*===============Specializing Hypotheses============*)

Theorem specialize_example: forall n,
  (forall m, m * n = 0) ->
  n = 0.
Proof.
  intros n H.
  specialize H with (m := 1).
  rewrite mult_1_l in H.
  apply H. 
Qed.

Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (*
  a, b, c, d, e, f : nat
  eq1 : [a; b] = [c; d]
  eq2 : [c; d] = [e; f]

  goal: [a; b] = [e; f]
  *)

  specialize trans_eq with (y:=[c;d]) as H. 
  (* Added:
   H : forall x z : list nat, x = [c; d] -> [c; d] = z -> x = z
  *)
  apply H.
  (* goals:
   [a; b] = [c; d]

   [c; d] = [e; f]
  *)

  apply eq1.
  apply eq2. 
Qed.


(*========Varying the Induction Hypothesis==============*)

Theorem double_injective: forall n m,
         double n = double m ->
         n = m.
Proof.
intros n m. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.
  - (* n = S n' *) intros eq. destruct m as [| m'] eqn:E.
    + (* m = O *) discriminate eq.
    + (* m = S m' *) f_equal.
(*At this point, the induction hypothesis (IHn') does not give us n' = m'
 -- there is an extra S in the way --  so the goal is not provable.*)
Abort.


Theorem double_injective': forall n m,
         double n = double m ->
         n = m.
Proof.
intros n. induction n as [ | n' IHn'].
 - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
   + (* m = O *) reflexivity.
   + (* m = S m' *) discriminate eq.
 - (* n = S n' *) intros m eq. destruct m as [| m'] eqn:E.
   + discriminate.
   + f_equal. apply IHn'. simpl in eq. injection eq as goal. apply goal.
Qed.

(*Exercise: 2 stars, standard (eqb_true)*)
Theorem eqb_true : forall n m,
  n =? m = true -> n = m.
Proof.
 intros n. induction n.
 - intros m. destruct m.
  + reflexivity.
  + simpl. discriminate.
 - intros m eq. destruct m.
  + simpl. discriminate.
  + simpl in eq. f_equal. rewrite <- IHn. reflexivity. apply eq.
Qed.

(*Exercise: 2 stars, advanced (eqb_true_informal)*)
(*
 Informal proof:

 n=0, m=0, so n=?m = true, therefore n=m
 n=0, m not 0, so n=?m = false, therefore n<>m
 n not 0, m=0, so n=?m = false, therefore n<>m
 n not 0, m not 0, but n=?m = true only in one case then n=m by def n?=m.
*)


Definition manual_grade_for_informal_proof : option (nat*string) := None.

(*Exercise: 3 stars, standard, especially useful (plus_n_n_injective)*)

Check plus_n_Sm.
(* forall n m : nat, S (n + m) = n + S m *)
Check f_equal.
(*: forall (A B : Type) (f : A -> B) (x y : A), x = y -> f x = f y*)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
 intros n. induction n.
 - intros m eq. simpl in eq. destruct m.
  + reflexivity.
  + discriminate.
 - intros m. destruct m.
  + simpl. rewrite <- plus_n_Sm. discriminate.
  + simpl. rewrite <- plus_n_Sm. rewrite <- plus_n_Sm.
    intros eq. apply f_equal. (*n=m | eq : S (S (n + n)) = S (S (m + m))*)
    injection eq as goal. (* goal : n + n = m + m *)
    rewrite <- IHn. reflexivity. apply goal.
Qed.

(*===========generalize=================*)

Theorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
  (* Now n is back in the goal and we can do induction on
     m and get a sufficiently general IH. *)
  induction m as [| m' IHm'].
  - (* m = O *) simpl. intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) reflexivity.
    + (* n = S n' *) discriminate eq.
  - (* m = S m' *) intros n eq. destruct n as [| n'] eqn:E.
    + (* n = O *) discriminate eq.
    + (* n = S n' *) f_equal.
      apply IHm'. injection eq as goal. apply goal. 
Qed.

(*Rewriting with conditional statements*)


Lemma sub_add_leb : forall n m, 
 n <=? m = true -> (m - n) + n = m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - (* n = 0 *)
    intros m H. rewrite add_0_r. destruct m as [| m'].
    + (* m = 0 *)
      reflexivity.
    + (* m = S m' *)
      reflexivity.
  - (* n = S n' *)
    intros m H. destruct m as [| m'].
    + (* m = 0 *)
      simpl. discriminate.
    + (* m = S m' *)
      simpl in H. simpl. rewrite <- plus_n_Sm.
(*if we rewrite with a conditional statement of the form P → a = b, 
then Coq tries to rewrite with a = b, and then asks us 
to prove P in a new subgoal. *)
 rewrite IHn'.
   * reflexivity.
   * apply H.
Qed.

(*Exercise: 3 stars, standard, especially useful (gen_dep_practice)*)

Theorem nth_error_after_last: forall (n : nat) (X : Type) (l : list X),
  length l = n ->
  nth_error l n = None.
Proof.
 intros l. induction l as [|l' IHl'].
 - intros. destruct l.
  + reflexivity.
  + simpl. discriminate.
 - intros. destruct l.
  + reflexivity.
  +  simpl. rewrite IHl'.
    * reflexivity.
    * simpl in H. injection H as goal. apply goal.
Qed. 

(*=========Unfolding Definitions============*)

Definition square n := n * n.


Lemma square_mult : forall n m, square (n * m) = square n *square m.
Proof.
  intros n m.
  unfold square.
  rewrite mult_assoc.
  assert (H : n * m * n = n * n * m).
  { rewrite mul_comm. apply mult_assoc. }
  rewrite H. rewrite mult_assoc. reflexivity.
Qed.

Definition foo (x: nat) := 
 match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  unfold foo. destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.

(*==========destruct on Compound Expressions=========*)
Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (n =? 3) eqn:E1.
    - (* n =? 3 = true *) reflexivity.
    - (* n =? 3 = false *) destruct (n =? 5) eqn:E2.
      + (* n =? 5 = true *) reflexivity.
      + (* n =? 5 = false *) reflexivity. 
Qed.

(*Exercise: 3 stars, standard (combine_split)*)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
 intros X Y l.
  induction l.
  - intros l1 l2 H. simpl in H. injection H as H. rewrite <- H. rewrite <- H0. reflexivity.
  - destruct x as (x, y).
    destruct l1 as [| x'].
    + intros l2 H. simpl in H. destruct (split l) in H. discriminate H.
    + destruct l2 as [| y'].
      * intros H. simpl in H. destruct (split l) in H. discriminate H.
      * intros H. simpl.
        assert (G: split l = (l1, l2)). {
          simpl in H. destruct (split l).
          injection H as H. rewrite -> H0. rewrite -> H2. reflexivity.
        }
        apply IHl in G.
        simpl in H. destruct (split l) in H. injection H as H.
        rewrite G. rewrite <- H. rewrite <- H1. reflexivity.
Qed.

(*
pair (cons x (fst (pair x0 y0))) (cons y (snd (pair x0 y0))) = pair (cons x' l1) (cons y' l2)
H : (x :: fst (x0, y0), y :: snd (x0, y0)) = (x' :: l1, y' :: l2)

injection H as H

H : x = x'
H0 : x0 = l1
H1 : y = y'
H2 : y0 = l2*)

(*Exercise: 2 stars, standard (destruct_eqn_practice)*)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
 intros f b. destruct b eqn:Eq. destruct (f true) eqn:T.
 - destruct (f false) eqn:F. 
  + rewrite T. rewrite T. reflexivity.
  + rewrite T. rewrite T. reflexivity.
 - destruct (f false) eqn:F.
  +  rewrite <- T. reflexivity.
  + rewrite F. reflexivity.
 - destruct (f false) eqn:F.
  + destruct (f true) eqn:T.
   * rewrite T. reflexivity.
   * rewrite <- F. reflexivity.
  + destruct (f true) eqn:T.
   * destruct (f false) eqn: F1. 
      rewrite T. rewrite F. reflexivity.
   rewrite F1. reflexivity.
   * destruct (f false) eqn: F1. 
      rewrite T. reflexivity.
   rewrite F1. reflexivity.
Qed.

(*===============Additional Exercises============*)

(*Exercise: 3 stars, standard (eqb_sym)*)
Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
 intros n m.
 destruct (n =? m) eqn:E.
 - symmetry. apply eqb_true in E. rewrite E. apply eqb_refl. 
 - generalize dependent m. induction n.
  + destruct m. 
   * discriminate.
   * reflexivity.
  + destruct m. 
   * reflexivity.
   * intros E. simpl in E.  simpl. rewrite <- IHn. reflexivity. apply E.
Qed.


(*Exercise: 3 stars, standard, optional (eqb_trans)*)
Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
 intros. apply eqb_true in H. apply eqb_true in H0. rewrite H. rewrite H0. apply eqb_refl.
Qed.

(*Exercise: 3 stars, advanced (split_combine)*)

Definition split_combine_statement : Prop :=
  (* (": Prop" means that we are giving a name to a
     logical proposition here.) *)
forall X Y (l1 : list X) (l2 : list Y), length l1 = length l2 -> split (combine l1 l2) = (l1, l2).


Theorem split_combine : split_combine_statement.
Proof.
 unfold split_combine_statement. 
 intros X Y. induction l1.
 - simpl. induction l2.
  + simpl. reflexivity.
  +  simpl. discriminate.
 - intros l2 H. destruct l2.
  + simpl. discriminate.
  + injection H as goal. apply IHl1 in goal. simpl. rewrite goal. reflexivity.
Qed. 

(* Do not modify the following line: *)
Definition manual_grade_for_split_combine : option (nat*string) := None. 

(*Exercise: 3 stars, advanced (filter_exercise)*)
Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf ->
  test x = true.
Proof.
 intros X test x l lf.
 destruct l as [| x'].
 - simpl. discriminate.
 - induction (x' :: l).
  + simpl. discriminate.
  + simpl. destruct (test x0) eqn:T.
    * intros H. injection H as H. rewrite -> H in T. apply T.
    * apply IHl0. 
Qed.













