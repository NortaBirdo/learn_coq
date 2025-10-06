
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