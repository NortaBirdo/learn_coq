Module Playground.
    Inductive rgb : Type :=
    | blue
    | red.

    Definition b : rgb := blue.
End Playground.

Definition b : bool := true.

Check b : bool.
Check Playground.b : Playground.rgb.