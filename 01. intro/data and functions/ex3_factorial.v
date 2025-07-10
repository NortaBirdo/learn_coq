Fixpoint plus (n m : nat) : nat :=
match m with 
| S m' => S (plus n m')
| O => n
end.

Compute (plus 2 3).

Fixpoint mult (n m : nat) : nat :=
match m with
| 0 => 0
| S m' => plus n (mult n m')
end. 

Compute mult 2 3.

Fixpoint factorial (n: nat) : nat :=
 match n with 
 | O => 1
 | S n' => mult n (factorial n')
 end.

Compute factorial 0.
Compute factorial 1.
Compute factorial 2.
Compute factorial 3.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.