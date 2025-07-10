# Vernacular command

`Admitted`. Just trust me)
`Check` - print the type
`Inductive` - register a new type: Inductive <name> : Type := <definition> .
`Definition` - register a function: Definition <func_name> (<param_name>:<param_type>) : <return_type> := <...> .
`Definition` second options: Definition <func_name> (<param_name> <param_name> : <param_type>) : <return_type> := <...> .
`Compute` - run a function: Compute (<function name> <function arg>).
`Example` - unittest for coq. Example <example_name>: <function call> = <expected_result>.
`Arguments` - id {A} a. It says the param `a` is implicit. for function `A`.

# Types

Every expression in Coq has a type describing what sort of thing it computes. The `Check` command asks Coq to print the type of an expression. Example: `Check (negb true) : bool.`

# Modules

<pre>
Module Playground.
  Definition foo : rgb := blue.
End Playground.
Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.
</pre>\

# If

<pre>
Definition andb (a b : bool) : bool :=
if a then b
else true.
</pre>

# Pattern matching

Two options:

<pre>
Definition andb (b c : bool): bool := 
 match b with
| true => c
| false => false
end.
</pre>

<pre>
Definition andb (a b : bool): bool := 
 match a, b with
| true, true => true
| true, false => false
| false, false => false
| false, true => false
end.
</pre>

They are not equal from calculations' effectiveness and proof perspective.


# comparing notations
`=` is a logical claim that we can attempt to prove.
`=?`, `<=?` is an expression that Coq computes.

# Notations
Example:
<pre>
Notation "x + y" := (plus x y) (at level 50, left associativity)
</pre>

where:
* `at level 50` - **precedence level**, it uses numbers from 0 to 100. Less goes first.
* `left associativity` - **associativity**. The associativity setting helps to disambiguate expressions containing multiple occurrences of the same symbol. Possible values:  `left`, `right`, `no`.

Each notation symbol is also associated with a *notation* scope. Coq tries to guess what scope is meant from context. Occasionally, it is necessary to help it out by writing, for example, `(x×y)%nat`, and sometimes in what Coq prints it will use %nat to indicate what scope a notation is in.

Pro tip: Coq's notation mechanism is not especially powerful. Don't expect too much from it.