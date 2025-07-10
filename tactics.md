
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


## Intro
`intros n` moves n from the quantifier in the goal to a *context* of current assumptions.

## Reduction tactics
`simpl` was just added so that we could see the intermediate state, after simplification but before finishing the proof. Is used in situations where we may have to read and understand the new goal that it creates, so we would not want it blindly expanding definitions and leaving the goal in a messy state. **Human readable** smart choice about reductions. Except: delta reduction or iota is immediately triggered.

`cbn` (call by name) newer that simpl. smarter.

`cbv` (call by value) fully compute. Takes flags to selectivity enable each kind of reduction.

`compute` is shorthand for beta-delta-iota-zeta reductions

`reflexivity` will do some simplification automatically when checking that two sides are equal. It does somewhat more simplification than simpl does -- for example, it tries "unfolding" defined terms, replacing them with their right-hand sides. The reason for this difference is that, if reflexivity succeeds, the whole goal is finished and we don't need to look at whatever expanded expressions. In other words:
* to prove e1=e2, fully reduce e1 and e2
* if the result are alpha-equivalent, succeed.

The `=` means that e1 and e2 definitionally equal (convertible). Convertibiliy is *decidable* in Coq, that's what reflexivity does.

## rewrite
`rewrite term` replaces n with m in the goal statement and obtain an equality with the same expression on both sides. Term must have a form: `forall (x1 :A1 ) ... (xn :An ). eq term1 term2`

## destruct aka case analysis

The syntax:

<pre>
destruct b eqn:E.
  - reflexivity.
  - reflexivity.
</pre>

shortcuts: `intros [|n].` if the variable needs a name.
`intros []` if it doesn't

you may use the following symbols for destruct: -, +, *, {}, and their repetition such as ++.