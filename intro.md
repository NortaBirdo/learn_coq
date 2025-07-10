# Theoretical basis

## History

**Kurt Gödel** shows (1931) that any logic strong enough to reasoning about arithmetic must be incomplete. There will be proposition that can neither be proved nor disproved. [Source](https://en.wikipedia.org/wiki/G%C3%B6del%27s_incompleteness_theorems)

**Alan Turing** shows (1936) that halting problem is undecidable. 
* Halting problem is the problem of determining, from a description of an arbitrary computer program and an input, whether the program will finish running, or continue to run forever.

**Rice's theorem**. In 1951 Golden-Rice states that all non-trivial semantic properties of programs are undecidable (not only the halt). [Source](https://en.wikipedia.org/wiki/Rice%27s_theorem) Where:
* *Trivial* is "all programs are true" or "all programs are false" 
* *undecidable* is a decision problem for which it is proved to be impossible to construct an algorithm that always leads to a correct yes-or-no answer. [Source](https://en.wikipedia.org/wiki/Undecidable_problem)

*Despite that we can't achieve the perfect result. We are able to get usefulness in every day affairs.* Successful story:
* TLA+ (Intel, Microsoft, Amazon) [source](https://ru.wikipedia.org/wiki/TLA%E2%81%BA)
* Coq (Calculus of Constructions, Thierry Coquand). CompCert (aviation, nuclear industry), seL4 (not Coq), Fiat Cryptography (Chrome), GCC (Airbus), Cryptocurrency
* F* is used by firefox for verify crypto code.

## Lambda Calculus

## Formal Verification
Formal Verification - a way to increase our insurance in quality of program. 
Validation a question of matching description and real world
Components:
* Specification. Description of the system by a formal language.
* Implementation
* Proof
* Checker

So formal proof:
* all steps are checked using initial axioms
* no appellation to intuition
* no exception.

# Tools overview

**Motivation**:
* bug free: Therac-25 (radiation), Arian-5, Mass Orbital, Patriot, F16 (sea-level)
* insight about software 

**Tools' classification**:
* Interactive theorem provers (Coq, Lean, F*, Isabell/HOL, Agda, Idris)
* Automated theorem prover (SAT, SMT)
* Specification languages and Model checking
* Program Logic (Флойда Хлора) 

10:1 proof code : prod code

**Limitations**:
* assumptions
* boundaries and stacked parts
* plugins
* your prove is strong as your spec is strong. That is not easy (think about business code, not compilers)

So you need proves and tests.


# Coq overview

Coq is based on:
* High-order constructivist logic. You may add your own axioms and down to formal set.
* Depended types
* Curry-Howard Correspondence:
  * Proposition is special case of types
  * proof checking - type checking
  * proving - programming

Coq is translated to Scala

Embedding. run other language to Coq (i.e. Go, OCaml, Haskell)

Coq is total language. A function must return something and all cases must be processed, and the program can't be cycled.

There are several languages inside Coq: 
**Vernacular** - the command language for Coq. Must be capitalized. It's a separate meta-language.
**Gallina** - language of terms such as match, if, forall etc (functional programming language). Gallina extends simple lambda-calculus, adds:
* Definitions (delta-reduction)
* Inductive types, pattern matching, recursion (iota reduction)
* Let bindings (zeta reduction)

**Ltac** - intros, simpl, reflexivity, etc. Language for tactics.

These languages are combined together. 

OPAM - OCalm Package Manager

# Reading

**Papers**:
1. "Formal Proof" Hales (2008)
1. "Position Papers. the science of deep specification". Appel (2017)
1. "QED and large: a survey of engineering of formally verified software". Ringer. (2019) 

**Books**:
1. Program and proofs. Mechanizing Mathematics with Depended Types. Sergey. (free)
1. (about the best Coq library) Mathematical Components Books. Mahboubi.
1. Coq Software Foundations

**Lectures**
1. The lecture of author of logical foundations. https://www.lektorium.tv/node/35485
1. Лекторий ComputerScienceCenter https://www.lektorium.tv/node/35486