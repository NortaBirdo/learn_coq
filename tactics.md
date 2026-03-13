
# Theorem

`Example`, `Theorem`, `Lemma`, `Fact`, and `Remark` have no difference from Coq perspective. But we use different names to emphasis reader attention.

The format is: 
<pre>
Theorem name_theorem : 
  (quantifier (variable : type), (proved statement)).
</pre>

Note! The parenthesis could be omitted.

# Tactics

Proof uses Tactics and has a structure: `Proof. <tactics>. Qed.`. You need an assumption (subgoal) before using it (for example stated example).

A `tactic` is a command that is used between `Proof` and `Qed` to guide the process of checking some claim we are making. 
`->` pronounce "implies"


## Intros
`intros n` moves n from the quantifier in the goal to a *context* of current assumptions.

## Reduction tactics (`simpl`, `reflexivity`)
`simpl` was just added so that we could see the intermediate state, after simplification but before finishing the proof. Is used in situations where we may have to read and understand the new goal that it creates, so we would not want it blindly expanding definitions and leaving the goal in a messy state. **Human readable** smart choice about reductions. Except: delta reduction or iota is immediately triggered.

`cbn` (call by name) newer that simpl. smarter.

`cbv` (call by value) fully compute. Takes flags to selectivity enable each kind of reduction.

`compute` is shorthand for beta-delta-iota-zeta reductions

`reflexivity` will do some simplification automatically when checking that two sides are equal. It does somewhat more **simplification and some kind of computation** than simpl does -- for example, it tries "unfolding" defined terms, replacing them with their right-hand sides. The reason for this difference is that, if reflexivity succeeds, the whole goal is finished and we don't need to look at whatever expanded expressions. In other words:
* to prove e1=e2, fully reduce e1 and e2
* if the result are alpha-equivalent, succeed.

The `=` means that e1 and e2 definitionally equal (convertible). Convertibiliy is *decidable* in Coq, that's what reflexivity does.

Hint: again, remember that reflexivity simplifies expressions a bit more aggressively than simpl.

## `rewrite`
`rewrite term` replaces n with m in the goal statement and obtain an equality with the same expression on both sides. Term must have a form: `forall (x1 :A1 ) ... (xn :An ). eq term1 term2`

If a hypothesis has the form H: P → a = b, then rewrite H will rewrite a to b in the goal, and add P as a new subgoal.

It is also additional syntax that helps the tactics to find out specific part of equation. Suppose we have: 

<pre>
((m * n) + ((m * p') * n)) = (((n * m) * p') + (n * m))
</pre>

applying instruction `rewrite (mul_comm (m * p') n).` leads to exchange in particular part of the goal:

<pre>
((m * n) + (n * (m * p'))) = (((n * m) * p') + (n * m))
</pre>

**Note** that parts of the pattern included several variable must be include in parentheses.

### applying from left and from right part `<-`, `->`

Let suppose that we have the following Lemma: `add_comm : ∀ a b, a + b = b + a`. The left part of the equation is `a+b` the right one is `b+a`.

From **left to right** (default, `->`). `rewrite` searches in the goal which fits to the left (`a+b`) pattern; transforms the found pattern according to the right part and substitutes into the goal. 

Goal before: `(n + m) + q = ?`; 
after `rewrite add_comm.` (Coq matches `a = n`, `b = m`)
Goal is: `(m + n) + q = ?`. 

From **right to the left** (`<-`, "do the rule backward"). It searches the pattern form the right part of the Lemma, transforms according to left and substitutes into the goal.

More complex example. Suppose in the goal we have:
 `... + ((n + m) * p) + (n + m) + ... = `
 
When we wrote: `rewrite (add_comm ((n + m) * p) (n + m)).` We told directly that `a = ((n + m) * p)` and `b = (n + m)` and both must be in `plus` operation. And since we didn't use arrow, the search pattern of the `add_comm` (`a + b`) will be done in the left part of the goal. As the result the goal will be rewritten as:
`...(n + m) + ((n + m) * p)...`.

### conditional

If we rewrite with a conditional statement of the form P → a = b, then Coq tries to rewrite with a = b, and then asks us to prove P in a new subgoal.

Short example. Suppose we have the hypotheses:

<pre>
 IHl' : forall (X : Type) (l : list X), length l = l' -> nth_error l l' = None
______________________________________
nth_error l l' = None
</pre>

after applying tactic `rewrite IHl'`. We'll have:

<pre>
______________________________________(1/2)
None = None
______________________________________(2/2)
length l = l'
</pre>

## `replace`
The replace tactic allows you to specify a particular subterm to 
rewrite and what you want it rewritten to: replace (t) with (u) replaces 
(all copies of) expression t in the goal by expression u, 
and generates t = u as an additional subgoal.

Suppose we have before applying: 
`((S n') + (m + p)) = (m + ((S n') + p))`

Applying: `replace (m + p) with (p + m).`

The result is:
`((S n') + (p + m)) = (m + ((S n') + p))`

## `destruct` aka case analysis

The syntax:

<pre>
destruct b eqn:E.
  - reflexivity.
  - reflexivity.
</pre>

shortcuts: `intros [|n].` if the variable needs a name.
`intros []` if it doesn't

you may use the following symbols for destruct: -, +, *, {}, and their repetition such as ++.

## `apply` a shortcut for `rewrite ... reflexivity`.

Typically, when we use apply H, the statement H will begin with a ∀ that introduces some universally quantified variables. When Coq matches the current goal against the conclusion of H, it will try to find appropriate values for these variables.

To use the apply tactic, the (conclusion of the) fact being applied must match the goal exactly (perhaps after simplification)

<pre>
Theorem silly1 : forall (n m : nat),
  n = m ->
  n = m.
Proof.
  intros n m eq.
  apply eq. (*rewrite → eq. reflexivity. *)
Qed.
</pre>

### apply with

Sometimes `apply` doesn't understand which variable must be used. Then there is a way to show it:

<pre>
Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (y:=[c;d]). 
  apply eq1. 
  apply eq2. 
Qed.
</pre>


## `symmetry`

Revert expression. Suppose in the goal `m = n` when after applying `symmetry` will be `n = m`.

## `transitivity `

A shortcut for case `a=b=c -> a=c`. The tactic requires us to state the instantiation we want, just like `apply with` does. Generates subgoals.

<pre>
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
 intros.
 transitivity m. 
 apply H0.
 apply H.
Qed.
</pre>

## `injection` 

**Shortly**: it is a way to proof something by removing constructors ("unpacking"). Of cause the constructors must be the same.  
If you have a hypothesis `C x1 ... xn = C y1 ... yn` there `C` - constructor. The tactic produces new hypotheses: `x1 = y1, ..., xn = yn`

The constructor S is injective (or one-to-one). That is, if S n = S m, it must also be that n = m. The constructors O and S are disjoint. That is, O is not equal to S n for any n. *All constructors are injective, and the values built from distinct constructors are never equal.*

To prove that you need to write and prove some theorem which undone application of constructor. Technically it can be done by a special function and appropriate theorem:

<pre>
Theorem S_injective : ∀ (n m : nat),
  S n = S m →
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.
</pre>

The `injection` tactic is a sortcut for that way:

<pre>
Theorem injection_ex1 : ∀ (n m o : nat),
  [n;m] = [o;o] →
  n = m.
Proof.
  intros n m o H.
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
</pre>

**More examples**
<pre>
Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.

Theorem bin_injective :
  forall b1 b2,
    B1 b1 = B1 b2 -> b1 = b2.
Proof.
 intros. 
 (*
  H : B1 b1 = B1 b2 
  --------
  b1 = b2
 *)
 injection H as eq. 
 (*
  eq : b1 = b2
  --------
  b1 = b2
  *)
 apply eq. 
Qed. 
</pre>

Two:
<pre>
Theorem color_injective :
  forall r1 g1 b1 r2 g2 b2,
    RGB r1 g1 b1 = RGB r2 g2 b2 ->
    r1 = r2 /\ g1 = g2 /\ b1 = b2.
Proof.
  intros r1 g1 b1 r2 g2 b2 H.
  (* H: RGB r1 g1 b1 = RGB r2 g2 b2 *)
  injection H as Hr Hg Hb.
  (* So now:
     Hr: r1 = r2
     Hg: g1 = g2  
     Hb: b1 = b2 *)
</pre>

Three
<pre>
(* DOESN'T WORK *)
Theorem bad_example :
  forall n, S n = S (n + 0) -> n = n + 0.
Proof.
  intros n H.
  injection H as H.  (* it creates n = n + 0, that is our goal already. *)
...
</pre>


## `discriminate`, principle of explosion

**Shortly**: it is a way to say "that's impossible (contradiction)". It works only if we check equity different inductive constructors. Coq doesn't allow to proof equation without contradiction.

The principle of disjointness says that two terms beginning with different constructors (like O and S, or true and false) can never be equal. This means that, any time we find ourselves in a context where we've assumed that two such terms are equal, we are justified in concluding anything we want, since the assumption is nonsensical.

The discriminate tactic embodies this principle: It is used on a hypothesis involving an equality between different constructors (e.g., false = true), and it solves the current goal immediately. 

<pre>
Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
 destruct n as [| n'] eqn:E.
  - (* n = 0 *)
    intros H. reflexivity.
  - (* S n = 0*) simpl. intros H. discriminate H.
Qed.
</pre>

One more example:
<pre>
Theorem disc_works : 
  forall n, S n = O -> False.
Proof.
  intros n H.
  discriminate H.  (* Успешно: S ≠ O *)
Qed.
</pre>

Negative example:
<pre>
Theorem disc_fails :
  forall n, S n = S n -> True.
Proof.
  intros n H.
  discriminate H.  (* ERROR: Not a discriminable equality *)
...
</pre>


## f_equal

if arguments of a function are the same, then the responses of the function are the same. 

<pre>
Theorem eq_implies_succ_equal' : ∀ (n m : nat),
  n = m → S n = S m.
Proof. intros n m H. f_equal. apply H. Qed.
</pre>

## Tactics in hypotheses, backward on forward reasoning

**Forward reasoning** is more used in classic math, then you modify premises until reach a goal. In other words, `apply L in H` gives us a form of "forward reasoning": given X → Y and a hypothesis matching X, it produces a hypothesis matching Y.

**Backward reasoning** is more suitable for formal proving. Then you modify goal until it fits with the original premises or another theorem. `apply L` is "backward reasoning": it says that if we know X → Y and we are trying to prove Y, it suffices to prove X.

`in` applies operations in context.

<pre>
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  (* EQ : n = m -> p = q
     H : m = n 
     goal: q = p*)

  symmetry in H.
  (*H : n = m*)

  apply EQ in H. 
  (*H : p = q*)
  
  symmetry in H.
  (*H : q = p*)
  apply H.
Qed.
</pre>

## `specialize`

 It is essentially just a combination of `assert` and `apply`, but it often provides a pleasingly smooth way to nail down overly general assumptions. If `H` is a quantified hypothesis in the current context, i.e 
 
 `H : ∀ (x:T), P` 
 
 then `specialize H with (x := e)` will change `H` so that it looks like `[x:=e]P`, that is, `P` with `x` replaced by `e`.

We can specialize facts in the global context, not just local hypotheses.
The as... clause at the end tells specialize how to name the new hypothesis in this case.

<pre>
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  (*
  a, b, c, d, e, f : nat
  eq1 : [a; b] = [c; d]
  eq2 : [c; d] = [e; f]
  goal: [a; b] = [e; f]
  *)

  specialize trans_eq with (y:=[c;d]) as H. 
  (* Added:
   H : forall x z : list nat, x = [c; d] -> [c; d] = z -> x = z
  *)

  apply H.
  (* goals:
   [a; b] = [c; d]

   [c; d] = [e; f]
  *)

  apply eq1.
  apply eq2. 
Qed.
</pre>

# generalize

`generalize expr as var_name.`

## Generalize part of expression
<pre>
Theorem example1 :
  forall x y, x + y = y + x -> (x + y) + (x + y) = (y + x) + (y + x).
Proof.
  intros x y H.
  (* goal: (x + y) + (x + y) = (y + x) + (y + x) *)
  generalize (x + y) as a.
  (* goal: forall a, a = y + x -> a + a = (y + x) + (y + x) *)
</pre>

## do induction by n, but save m

without generalization:
<pre>
Theorem generalize_for_induction :
  forall n m, n + m = m + n.
Proof.
  intros n m.
  (*goal: n + m = m + n*)
  induction n as [|n' IHn'].

</pre>

* `m : nat`
* goals:
  * `0 + m = m + 0`
  * `S n' + m = m + S n'`

With:
<pre>
Theorem generalize_for_induction :
  forall n m, n + m = m + n.
Proof.
  intros n m.
  (*goal: n + m = m + n*)
  generalize m as m'.
  (*goal: forall m' : nat, n + m' = m' + n*)
  induction n as [|n' IHn'].
</pre>

* `m : nat`
* goals:
  * `forall m' : nat, 0 + m' = m' + 0`
  * `forall m' : nat, S n' + m' = m' + S n'`


## generalize dependent

The strategy of doing fewer intros before an induction to obtain a more general IH doesn't always work; sometimes some rearrangement of quantified variables is needed. Suppose, for example, that we wanted to prove double_injective by induction on m instead of n.

<pre>
Theorem dependent_example :
  forall n m, n <= m -> n + n <= m + m.
Proof.
  intros n m H.
  (* induction by H,  but  n and m are fixed *)
  generalize dependent n.
  generalize dependent m.
  (* now goal is: forall m n, n <= m -> n + n <= m + m *)
  induction...
</pre>

Induction could work only with free variables. And for induction the *quantifier* (квантор) is needed. This tactics  allows **rearrangement of quantified variables**.

<pre>
heorem double_injective_take2 : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n m.
  (* n and m are both in the context *)
  generalize dependent n.
</pre>

The problem is that, to do induction on m, we must first introduce n. (If we simply say induction m without introducing anything first, Coq will automatically introduce n for us!)

# `unfold`

`unfold` allows go through definitions of functions and variables.

<pre>
Definition foo (x: nat) := 
 match x with
  | O => 5
  | S _ => 5
  end.

Fact silly_fact_2' : forall m, foo m + 1 = foo (m + 1) + 1.
Proof.
  intros m.
  unfold foo. destruct m eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
</pre>