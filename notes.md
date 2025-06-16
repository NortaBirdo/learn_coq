The `Admitted` command can be used as a placeholder for an incomplete proof. 

# Types

Every expression in Coq has a type describing what sort of thing it computes. The `Check` command asks Coq to print the type of an expression. Example: `Check (negb true) : bool.`

# modules

<pre>
Module Playground.
  Definition foo : rgb := blue.
End Playground.
Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.
</pre>\