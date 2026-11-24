Inductive nucleo : Type :=
  | A
  | T
  | G
  | C.

Inductive amino : Type :=
 | H
 | K.

Inductive triplet : Type :=
  | nil
  | cons (n : nucleo) (t : triplet).

Definition make_triplet (x y z : nucleo) : triplet :=
  (cons x (cons y (cons z nil))).

Notation "x - y - z" := (make_triplet x y z)
(at level 50, left associativity).
Definition AAA := A-A-A.
Check A.
Check H.
Check AAA.


Definition def_amiono (a : triplet) : amino := 
 match a with 
 | cons A (cons A (cons A nil)) => H
 | _ => K
 end.

 Compute def_amiono AAA.