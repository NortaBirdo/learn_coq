Module inititive.
    (*My own definition from scratch just for better training*)
    Fixpoint ltb (n m : nat) : bool :=
    match n, m with
    | O, O => false
    | O, S m' => true
    | S n', O => false
    | S n', S m' => ltb n' m'
    end.

    Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

    Example test_ltb1: (ltb 2 2) = false.
    Proof. simpl. reflexivity. Qed.
    Example test_ltb2: (ltb 2 4) = true.
    Proof. simpl. reflexivity. Qed.
    Example test_ltb3: (ltb 4 2) = false.
    Proof. simpl. reflexivity. Qed.

End inititive.

(*Now in the way I was asked for*)


