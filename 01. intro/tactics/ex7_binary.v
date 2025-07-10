Module binary.

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

Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z).
Proof. reflexivity. Qed.

Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B0 (B1 Z)).
Proof. reflexivity. Qed.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => plus n' (S m)
  end.

Fixpoint mult (m n : nat) : nat :=
  match m with
  | O => O
  | S m' => plus n (mult m' n)
  end.

Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B1 Z => S O
  | B1 m' => plus 1 (mult 2 (bin_to_nat m'))
  | B0 m' => mult 2 (bin_to_nat m')
  end.

Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2.
Proof. reflexivity. Qed.

Example test_bin_incr5 :
        bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.


Example test_bin_incr6 :
        bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z).
Proof. reflexivity. Qed.

End binary.