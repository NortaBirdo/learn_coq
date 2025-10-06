# Polymorphic list definition

<pre>
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
</pre>

"Type list is parametrized by X". List now is a type-level function.

 A good way to think about it is that the definition of list is a function from `Types` to `Inductive` definitions; or, to put it more concisely, list is a function from `Types` to `Types`.

 It helps avoiding repetition of constructors, functions and theorem for them. 

 The `X` in the definition of list automatically becomes a parameter to the constructors `nil` and `cons` -- that is, `nil` and `cons` are now polymorphic constructors; when we use them, we must now **provide a first argument** that is the type of the list they are building. For example, `nil nat` constructs the empty list of type `nat`: 
 
 <pre>
 Check (nil nat) : list nat.
 Check (cons nat 3 (nil nat)) : list nat.
 </pre>

 ## type inference

 Coq was able to use type inference to deduce what the types of X, x, and count must be, based on how they are used.

 <pre>
Fixpoint repeat' X x count : list X :=
  match count with
  | 0 ⇒ nil X
  | S count' ⇒ cons X x (repeat' X x count')
  end.
 </pre>

  Since X is used as an argument to cons, it must be a Type, since cons expects a Type as its first argument; matching count with 0 and S means it must be a nat; and so on.

  ## Type Argument Synthesis

To use a polymorphic function, we need to pass it one or more types in addition to its other arguments. The coq tries to fill information unifying all local information. That is why we can use "hole" `_` to avoid redundancy in passing arguments.

<pre>
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 ⇒ nil _
  | S count' ⇒ cons _ x (repeat'' _ x count')
  end.
</pre>

Instead
`Definition list123 := cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).`
we do
`Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).`

## Implicit Arguments

In fact, we can go further and even avoid writing _'s in most cases by telling Coq always to infer the type argument(s) of a given function.

The Arguments directive specifies the name of the function (or constructor) and then lists the (leading) argument names to be treated as implicit, each surrounded by curly braces.
<pre>
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
</pre>


## Supplying Type Arguments Explicitly

Sometimes the Coq stacks with type inference. Then we can put the type explicitly.

`Definition mynil : list nat := nil.`

OR put `@`

`Check @nil : ∀ X : Type, list X.`

### Fail instruction

The `Fail` qualifier that appears before Definition can be used with any command, and is used to ensure that that command indeed fails when executed. If the command does fail, Coq prints the corresponding error message, but continues processing the rest of the file.

`Fail Definition mynil := nil.` will lead to the message:

The command has indeed failed with message:

*The following term contains unresolved implicit arguments: nil. More precisely: - ?A: Cannot infer the implicit parameter A of nil whose type is "Type".*

### Annotation `type_scope`

The annotation `type_scope` tells Coq that this abbreviation should only be used when parsing types, not when parsing expressions. This avoids a clash with the multiplication symbol.

# Functions as Data

Functions that manipulate other functions are often called higher-order functions. Here's a simple one:

 <pre>
Definition doit3times {X : Type} (f : X→X) (n : X) : X :=
  f (f (f n)).
 </pre>

 Anonymous Functions are constructed by an expression:
 `(fun n ⇒ n * n)`

 Here is the filter example, rewritten to use an anonymous function.

<pre>
Example test_filter2':
    filter (fun l ⇒ (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
</pre>

# Functions That Construct Functions

Here is a function that takes a value x (drawn from some type X) and returns a function from nat to X that yields x whenever it is called, ignoring its nat argument.

<pre>
Definition constfun {X: Type} (x: X) : nat → X :=
  fun (k:nat) ⇒ x.


Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Example constfun_example2 : (constfun 5) 99 = 5.
</pre>

# partial application and curring

In fact, the multiple-argument functions we have already seen are also examples of passing functions as data. To see why, recall the type of plus.

`Check plus : nat → nat → nat.`

Each → in this expression is actually a binary operator on types. This operator is right-associative, so the type of plus is really a shorthand for nat Definition prod_uncurry {X Y Z : Type}
  (f : X → Y → Z) (p : X × Y) : Z→ (nat → nat) -- i.e., it can be read as saying that "plus is a one-argument function that takes a nat and returns a one-argument function that takes another nat and returns a nat." 

The type X → Y → Z can be read as describing functions that take two arguments, one of type X and another of type Y, and return an output of type Z. Strictly speaking, this type is written X → (Y → Z) when fully parenthesized. That is, if we have f : X → Y → Z, and we give f an input of type X, it will give us as output a function of type Y → Z. If we then give that function an input of type Y, it will return an output of type Z. That is, every function in Coq takes only one input, but some functions return a function as output. This is precisely what enables partial application, as we saw above with `plus3`.

By contrast, functions of type X × Y → Z -- which when fully parenthesized is written (X × Y) → Z -- require their single input to be a pair. Both arguments must be given at once; there is no possibility of partial application.

It is possible to convert a function between these two types. Converting from X × Y → Z to X → Y → Z is called **currying**, in honor of the logician Haskell Curry. Converting from X → Y → Z to X × Y → Z is called **uncurrying**.
