Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.


Definition orb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => true
  | false => b2
end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Notation "x || y" := (orb x y).
Example test_orb2: true || false = true.
Proof. simpl. reflexivity. Qed.

Definition andb (a b : bool) : bool :=
if a then b
else true.

Notation "x && y" := (andb x y).
Example test_and1 : true && false = false.
Proof. simpl. reflexivity. Qed.