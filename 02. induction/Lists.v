From LF Require Export Induction.

Module NatList.

(*The one and only way to construct a pair of 
numbers is by applying the constructor pair to two arguments of type nat.*)
Inductive natprod : Type := 
 | pair (n1 n2 : nat).

Check (pair 3 5) : natprod.

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

Compute (fst (pair 3 5)).
(* ===> 3 *)

Notation "( x , y )" := (pair x y).

Compute (fst (3,5)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n, m) = (fst (n,m), snd (n,m)).
Proof. reflexivity. Qed.


Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.


(*Exercise: snd_fst_is_swap*)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
 intros p. destruct p. simpl. reflexivity. Qed.

(*Exercise: fst_swap_is_snd*)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
 intros p. destruct p. simpl. reflexivity. Qed.

(*=========Lists of Numbers==========*)


Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).

(*definition of list of three elemetns*)

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(*These definitions are the same*)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].


Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.


Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil => l2
  | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).
Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tl (l : natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.


(*Exercise: 2 stars, standard, especially useful (list_funs)*)


Fixpoint nonzeros (l:natlist) : natlist :=
 match l with
 | nil => nil
 | h::t => match h with
           | O => nonzeros (t)
           | S b => h :: nonzeros (t)
           end
end.


Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.


Fixpoint oddmembers (l:natlist) : natlist :=
 match l with
 | nil => nil
 | h::t => match odd h with
           | true => h :: oddmembers (t)
           | false => oddmembers (t)
           end
end.


Example test_oddmembers: oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. simpl. reflexivity. Qed.

Definition countoddmembers (l:natlist) : nat :=
 length (oddmembers l).

Example test_countoddmembers1: 
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.

Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.

Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(*Exercise: 3 stars, advanced (alternate)*)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
 match l1 with
 | nil => l2
 | h1::t1 => match l2 with
    | nil => h1::t1
    | h2::t2 => h1 :: h2 :: (alternate t1 t2)
    end
end.


Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.


(*A bag (or multiset) is like a set, except that each element can 
appear multiple times rather than just once. One way of representating a bag of numbers is as a list.*)


Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
 match s with
 | nil => O
 | h::t => if h =? v then S (count v t) else count v t
end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof.  reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.


Definition sum : bag -> bag -> bag := app.


Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.


Definition add (v : nat) (s : bag) : bag :=
  cons (v) (s).

Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.


Fixpoint member (v : nat) (s : bag) : bool :=
 match s with
 | nil => false
 | h::t => if h =? v then true else member v t
end.


Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.


(*Exercise: 3 stars, standard, optional (bag_more_functions)*)

Fixpoint remove_one (v : nat) (s : bag) : bag := 
 match s with
 | nil => nil
 | h::t => if h =? v then t else h::(remove_one v t)
end.

Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. simpl. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.


Fixpoint remove_all (v:nat) (s:bag) : bag :=
match s with
 | nil => nil
 | h::t => if h =? v then remove_all v t else h::(remove_all v t)
end.

Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.


Fixpoint included (s1 : bag) (s2 : bag) : bool :=
 match s1 with
 | nil => true
 | h1::t1 => if member h1 s2 then included t1 (remove_one h1 s2) else false
end.

Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(*Exercise: 2 stars, standard, especially useful (add_inc_count)*)

Theorem add_inc_count : forall (v:nat) (s:bag),
  count v (add v s) = 1 + count v s.
Proof.
 intros. induction v.
 - simpl. reflexivity.
 - simpl. rewrite eqb_refl. reflexivity. (*Very interesting move - reduce condition*)
Qed.


(* Do not modify the following line: *)
Definition manual_grade_for_add_inc_count : option (nat*string) := None.

(*===================Reasoning About Lists==================*)

Theorem nil_app : forall l : natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. 
Qed.

(*Induction on Lists*)
Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite -> IHl1'. reflexivity. 
Qed.


Theorem repeat_double_firsttry : forall c n: nat,
  repeat n c ++ repeat n c = repeat n (c + c).
Proof.
  intros c. induction c as [| c' IHc'].
  - (* c = 0 *)
    intros n. simpl. reflexivity.
  - (* c = S c' *)
    intros n. simpl.
    (*  Now we seem to be stuck.  The IH cannot be used to 
        rewrite repeat n (c' + S c'): it only works
        for repeat n (c' + c'). If the IH were more liberal here
        (e.g., if it worked for an arbitrary second summand),
        the proof would go through. *)
Abort.

Theorem repeat_plus: forall c1 c2 n: nat,
    repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
Proof.
  intros c1 c2 n.
  induction c1 as [| c1' IHc1'].
  - simpl. reflexivity.
  - simpl.
    rewrite <- IHc1'.
    reflexivity.
  Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.
Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.


Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = n :: l' *)
    (* This is the tricky case.  Let's begin as usual
       by simplifying. *)
    simpl.
    (* Now we seem to be stuck: the goal is an equality
       involving ++, but we don't have any useful equations
       in either the immediate context or in the global
       environment!  We can make a little progress by using
       the IH to rewrite the goal... *)
    rewrite <- IHl'.
    (* ... but now we can't go any further. *)
Abort.

Theorem app_rev_length_S_firsttry: forall l n,
  length (rev l ++ [n]) = S (length (rev l)).
Proof.
  intros l. induction l as [| m l' IHl'].
  - (* l =  *)
    intros n. simpl. reflexivity.
  - (* l = m:: l' *)
    intros n. simpl.
    (* IHl' not applicable. *)
Abort.

Theorem app_length_S: forall l n,
  length (l ++ [n]) = S (length l).
Proof.
  intros l n. induction l as [| m l' IHl'].
  - (* l =  *)
    simpl. reflexivity.
  - (* l = m:: l' *)
    simpl.
    rewrite IHl'.
    reflexivity.
Qed.

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l' IHl'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons *)
    simpl.
    rewrite -> app_length_S.
    rewrite -> IHl'.
    reflexivity.
Qed.


Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons *)
    simpl. rewrite IHl1'. reflexivity. 
Qed.


(*How to use search*)

(*
Search rev.
Search (_ + _ = _ + _).
Search (_ + _ = _ + _) inside Induction.
Search (?x + ?y = ?y + ?x).*)

(*The question mark in front of the variable is needed to 
indicate that it is a variable in the search pattern, rather 
than a defined identifier that is expected to be in scope currently.*)

(*============List Exercises, Part 1=======================*)
(*Exercise: 3 stars, standard (list_exercises)*)
Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
 intros l. induction l.
 - reflexivity.
 - simpl. rewrite IHl. reflexivity. 
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
 intros l1 l2. induction l1.
 - simpl. rewrite app_nil_r. reflexivity.
 - simpl. rewrite IHl1. rewrite app_assoc. reflexivity.
Qed.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
 intros l. induction l.
 - simpl. reflexivity.
 - simpl. rewrite rev_app_distr. rewrite IHl. simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
 intros. induction l1.
 - simpl. rewrite app_assoc. reflexivity.
 - simpl. rewrite app_assoc. rewrite app_assoc. reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
 intros. induction l1.
 - simpl. reflexivity.
 - simpl. induction n.
  + rewrite IHl1. reflexivity.
  + simpl. rewrite IHl1. reflexivity.
Qed.


(*Exercise: 2 stars, standard (eqblist)*)
Fixpoint eqblist (l1 l2 : natlist) : bool := 
 match l1, l2 with
 | nil, nil => true
 | nil, h2::t2 => false
 | h1::t1, nil => false
 | h1::t1, h2::t2 => if h1 =? h2 then eqblist t1 t2 else false
end.


Example test_eqblist1 :
  (eqblist nil nil = true).
Proof.  reflexivity. Qed.
Example test_eqblist2 :
  eqblist [1;2;3] [1;2;3] = true.
Proof.  reflexivity. Qed.
Example test_eqblist3 :
  eqblist [1;2;3] [1;2;4] = false.
Proof.  reflexivity. Qed.

Theorem eqblist_refl : forall l:natlist,
  true = eqblist l l.
Proof.
 intros. induction l.
 - simpl. reflexivity.
 - simpl. rewrite eqb_refl. rewrite <- IHl. reflexivity.
Qed.
 
(*
add_inc_count : forall (v:nat) (s:bag), count v (add v s) = 1 + count v s.
nil_app : forall l : natlist, [] ++ l = l.
tl_length_pred : forall l:natlist, pred (length l) = length (tl l).
app_assoc : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
repeat_plus: forall c1 c2 n: nat, repeat n c1 ++ repeat n c2 = repeat n (c1 + c2).
app_length_S: forall l n, length (l ++ [n]) = S (length l).
rev_length : forall l : natlist, length (rev l) = length l.
app_length : forall l1 l2 : natlist, length (l1 ++ l2) = (length l1) + (length l2).
app_nil_r : forall l : natlist,  l ++ [] = l.
rev_app_distr: forall l1 l2 : natlist, rev (l1 ++ l2) = rev l2 ++ rev l1.
rev_involutive : forall l : natlist,  rev (rev l) = l
app_assoc4 : forall l1 l2 l3 l4 : natlist, l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
nonzeros_app : forall l1 l2 : natlist, nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2)
*)


