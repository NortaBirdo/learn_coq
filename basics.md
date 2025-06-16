Vernacular - the command for Coq. Must be capitalized. It's a separate meta-language.
Gallina - language of terms.
These languages are combined together. 

OPAM - OCalm Package Manager

`Admitted`. Just trust me)
`Check` - print the type
`Inductive` - register a new type: Inductive <name> : Type := <definition> .
`Definition` - register a function: Definition <func_name> (<param_name>:<param_type>) : <return_type> := <...> .
`Definition` second options: Definition <func_name> (<param_name> <param_name> : <param_type>) : <return_type> := <...> .
`Compute` - run a function: Compute (<function name> <function arg>).
`Example` - unittest for coq. Example <example_name>: <function call> = <expected_result>.
`Arguments` - id {A} a. It says the param `a` is implicit. for function `A`.

`Notation "A * B" := (prod A B) (at level 40, left associativity): type scope`

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

# Proof

Proof uses Tactics and has a structure: `Proof. <tactics>. Qed.`. You need an assumption (subgoal) before using it (for example stated example)

`simple`. This tactics means "simplify". Like (2+2*4 => 10)
`reflexivity` checks that u=v are convertible and then solves the goal.