# Complete Guide to Coq and This Verification Project

## Table of Contents
1. [Introduction to Coq](#introduction-to-coq)
2. [Project Overview](#project-overview)
3. [Basics Module](#basics-module)
4. [Imp Module](#imp-module)
5. [Langs Module](#langs-module)
6. [Code Analysis and Issues](#code-analysis-and-issues)
7. [Learning Path](#learning-path)
8. [Resources](#resources)

---

## Introduction to Coq

### What is Coq?

Coq is an **interactive theorem prover** and **proof assistant** developed in France. It allows you to:
- Write mathematical definitions and theorems
- Prove theorems with the assistance of a computer
- Write programs and prove they are correct
- Mechanically verify properties of software and hardware

### Core Concepts

#### 1. **The Curry-Howard Correspondence**
Coq is based on a deep principle: **proofs are programs, and programs are proofs**. This means:
- A theorem is like a type
- A proof is like a program that has that type
- Proving a theorem = constructing a term of that type

#### 2. **Dependent Types**
Coq uses a powerful type system where types can depend on values. For example:
```coq
Fixpoint replicate (n : nat) (x : nat) : list nat
```
The return type (`list nat`) could depend on the value of `n`.

#### 3. **Inductive Types**
Most data structures in Coq are defined inductively:
```coq
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
```
This says: a natural number is either zero (`O`) or the successor (`S`) of another natural number.

#### 4. **Tactics**
To prove theorems, you use **tactics** that manipulate proof goals:
- `intro` / `intros`: Introduce variables/hypotheses
- `simpl`: Simplify expressions
- `reflexivity`: Prove equality by computation
- `induction`: Apply induction principle
- `rewrite`: Rewrite using an equation
- `apply`: Apply a lemma or constructor
- `congruence`: Automated equality reasoning
- `lia`: Linear integer arithmetic solver

---

## Project Overview

This project is a **mini verification lab** exploring three areas:
1. **Basics**: Foundational proof techniques (induction, list manipulation, automation)
2. **Imp**: Formal semantics of a simple imperative language
3. **Langs**: Correctness of automata and parsers

---

## Basics Module

### File: `Basics/InductionLists.v`

#### What it Proves

This file proves fundamental properties of list operations using **structural induction**.

#### Key Definitions

1. **`app` (append)**: Concatenates two lists
```coq
Fixpoint app {A} (xs ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: app xs' ys
  end.
```

2. **`rev` (reverse)**: Reverses a list
```coq
Fixpoint rev {A} (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]
  end.
```

3. **`count`**: Counts occurrences of an element
```coq
Fixpoint count (x : nat) (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | y :: ys => (if Nat.eqb x y then 1 else 0) + count x ys
  end.
```

4. **`replicate`**: Creates a list of `n` copies of `x`
```coq
Fixpoint replicate (n x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: replicate n' x
  end.
```

#### Key Theorems

1. **`app_nil_r`**: Appending empty list is identity
```coq
Lemma app_nil_r : forall (A : Type) (xs : list A),
  app xs [] = xs.
```
**Proof technique**: Induction on `xs`.
- Base case: `app [] [] = []` by definition
- Inductive case: `app (x :: xs) [] = x :: app xs []` → use IH

2. **`app_assoc`**: Append is associative
```coq
Lemma app_assoc : forall (A : Type) (xs ys zs : list A),
  app xs (app ys zs) = app (app xs ys) zs.
```
**Proof technique**: Induction on `xs`, using `simpl` and `congruence`.

3. **`rev_app_distr`**: Reverse distributes over append
```coq
Lemma rev_app_distr : forall (A : Type) (xs ys : list A),
  rev (app xs ys) = app (rev ys) (rev xs).
```
**Proof technique**: Induction on `xs`, using `app_assoc` and `app_nil_r`.

4. **`rev_involutive`**: Reversing twice gives original list
```coq
Lemma rev_involutive : forall (A : Type) (xs : list A),
  rev (rev xs) = xs.
```
**Proof technique**: Induction on `xs`, using `rev_app_distr`.

5. **`count_replicate`**: Counting in replicated list
```coq
Lemma count_replicate :
  forall n x,
    count x (replicate n x) = n.
```
**Proof technique**: Induction on `n`, using `Nat.eqb_refl` and `lia` for arithmetic.

#### How the Code Works

The proofs follow the **principle of structural induction**:
1. **Pattern match** on the structure of the data (empty list vs. cons)
2. **Base case**: Prove for empty list (usually trivial)
3. **Inductive case**: Assume property holds for smaller lists (induction hypothesis), prove for larger list

Example proof flow for `app_nil_r`:
```coq
Proof.
  intros A xs.
  induction xs as [| x xs' IH].  (* Split into [] and x::xs' cases *)
  - (* Base: xs = [] *)
    simpl. reflexivity.
  - (* Inductive: xs = x :: xs' *)
    simpl.  (* app (x :: xs') [] = x :: app xs' [] *)
    rewrite IH.  (* Use IH: app xs' [] = xs' *)
    reflexivity.
Qed.
```

#### Current Status
✅ **All theorems fully proved** - No issues

---

### File: `Basics/Automation.v`

#### What it Does

This file demonstrates **proof automation** using Ltac (Coq's tactic language).

#### Key Concepts

1. **Hint Databases**: Collections of lemmas Coq can automatically apply
```coq
Hint Rewrite app_nil_r : list_rw.
```

2. **Custom Tactics**: User-defined proof procedures
```coq
Ltac crush :=
  repeat (simpl in *; subst; try rewrite ?app_nil_r in *;
          try autorewrite with list_rw in *;
          try lia; try congruence).
```

#### How the `crush` Tactic Works

The `crush` tactic combines multiple proof strategies:
- `repeat (...)`: Keep applying tactics until they stop working
- `simpl in *`: Simplify all expressions
- `subst`: Substitute equalities
- `try rewrite ?app_nil_r in *`: Try to rewrite using `app_nil_r` everywhere
- `autorewrite with list_rw`: Apply rewrite rules from `list_rw` hint database
- `lia`: Solve linear arithmetic goals
- `congruence`: Solve equality goals

#### Example: `demo_arith_list`

```coq
Lemma demo_arith_list :
  forall (xs : list nat),
    length (app xs []) + 0 = length xs.
Proof.
  intros xs.
  crush.  (* Automatically solves the goal! *)
Qed.
```

**How it works**:
1. `app xs []` rewrites to `xs` (using `app_nil_r`)
2. `length xs + 0` simplifies to `length xs` (using `lia`)
3. `reflexivity` concludes `length xs = length xs`

#### Current Status
✅ **Fully functional** - Demonstrates Ltac automation techniques

---

### File: `Basics/InductionListsTest.v`

#### What it Does

This file tests the functions defined in `InductionLists.v` using:
1. **`Compute` commands**: Execute functions and see results
2. **Example theorems**: Apply proven lemmas to concrete cases

#### Test Cases

```coq
Compute app [1; 2; 3] [4; 5; 6].
(* Result: [1; 2; 3; 4; 5; 6] *)

Compute rev [1; 2; 3; 4].
(* Result: [4; 3; 2; 1] *)

Compute count 3 [1; 2; 3; 3; 4; 3].
(* Result: 3 *)
```

#### Current Status
✅ **All tests pass** - Functions work correctly

---

## Imp Module

The Imp module implements a **small-step operational semantics** for a simple imperative language.

### File: `Imp/Syntax.v`

#### What it Defines

The abstract syntax of a tiny imperative language with:
- Arithmetic expressions (`aexp`)
- Boolean expressions (`bexp`)
- Commands (`com`)

#### Type Definitions

1. **Arithmetic Expressions**
```coq
Inductive aexp : Type :=
| ANum  : nat -> aexp           (* Constants: 42 *)
| AVar  : var -> aexp           (* Variables: x *)
| APlus : aexp -> aexp -> aexp  (* Addition: e1 + e2 *)
| AMinus: aexp -> aexp -> aexp  (* Subtraction: e1 - e2 *)
| AMult : aexp -> aexp -> aexp. (* Multiplication: e1 * e2 *)
```

2. **Boolean Expressions**
```coq
Inductive bexp : Type :=
| BTrue  : bexp                 (* true *)
| BFalse : bexp                 (* false *)
| BEq    : aexp -> aexp -> bexp (* e1 = e2 *)
| BLe    : aexp -> aexp -> bexp (* e1 <= e2 *)
| BNot   : bexp -> bexp         (* not b *)
| BAnd   : bexp -> bexp -> bexp.(* b1 and b2 *)
```

3. **Commands**
```coq
Inductive com : Type :=
| CSkip   : com                     (* skip *)
| CAss    : var -> aexp -> com      (* x := e *)
| CSeq    : com -> com -> com       (* c1; c2 *)
| CIf     : bexp -> com -> com -> com (* if b then c1 else c2 *)
| CWhile  : bexp -> com -> com.     (* while b do c *)
```

4. **State**: Maps variables to values
```coq
Definition state := var -> nat.

Definition update (st : state) (x : var) (n : nat) : state :=
  fun y => if String.eqb y x then n else st y.
```

#### Purpose

This defines the **abstract syntax tree (AST)** representation of programs. It's purely syntactic - no execution semantics yet.

#### Current Status
✅ **Complete** - Provides foundation for semantics

---

### File: `Imp/SmallStep.v`

#### What it Proves

This file defines **small-step operational semantics** for arithmetic expressions and proves properties about evaluation.

#### Small-Step Semantics

**Idea**: Instead of evaluating an expression in one big step, we define **single-step reductions**.

#### Key Definitions

1. **Value Predicate**: An expression is a value if it's fully evaluated
```coq
Definition is_value (a : aexp) : Prop :=
  match a with
  | ANum _ => True  (* Numbers are values *)
  | _ => False      (* Everything else needs reduction *)
  end.
```

2. **Step Relation** `a --> b`: Expression `a` reduces to `b` in one step
```coq
Inductive step : aexp -> aexp -> Prop :=
| ST_PlusConstConst : forall n1 n2,
    APlus (ANum n1) (ANum n2) --> ANum (n1 + n2)
    
| ST_Plus1 : forall a1 a1' a2,
    a1 --> a1' ->
    APlus a1 a2 --> APlus a1' a2
    
| ST_Plus2 : forall n1 a2 a2',
    a2 --> a2' ->
    APlus (ANum n1) a2 --> APlus (ANum n1) a2'
```

**How to read these rules**:
- `ST_PlusConstConst`: If both operands are numbers, compute the result
- `ST_Plus1`: If left operand can step, step it first
- `ST_Plus2`: If left is a value, step the right operand

Similar rules exist for multiplication (`ST_MultConstConst`, `ST_Mult1`, `ST_Mult2`).

3. **Multi-Step Relation** `a -->* b`: Expression `a` reduces to `b` in zero or more steps
```coq
Inductive multi : aexp -> aexp -> Prop :=
| multi_refl : forall a,
    multi a a
| multi_step : forall a b c,
    a --> b ->
    multi b c ->
    multi a c.
```

#### Example Evaluations

1. **Simple addition**: `3 + 4 --> 7`
```coq
Example test_step_simple :
  APlus (ANum 3) (ANum 4) --> ANum 7.
Proof.
  apply ST_PlusConstConst.
Qed.
```

2. **Complex expression**: `(2 + 3) * 4 -->* 20`
```coq
Example test_multistep :
  multi (AMult (APlus (ANum 2) (ANum 3)) (ANum 4))
        (ANum 20).
Proof.
  eapply multi_step. apply ST_Mult1. apply ST_PlusConstConst.
  (* (2 + 3) * 4 --> 5 * 4 *)
  eapply multi_step. apply ST_MultConstConst.
  (* 5 * 4 --> 20 *)
  apply multi_refl.
  (* 20 -->* 20 *)
Qed.
```

#### Evaluation Strategy

The semantics implements a **left-to-right, call-by-value** strategy:
1. Evaluate left operand to a value
2. Then evaluate right operand to a value
3. Finally, compute the operation

#### Key Properties (Not Yet Proved)

Standard properties that should be proved:
1. **Determinism**: If `a --> b` and `a --> c`, then `b = c`
2. **Progress**: If `a` is not a value, then exists `b` such that `a --> b`
3. **Values Don't Step**: If `is_value a`, then there's no `b` such that `a --> b`

#### Current Status
✅ **Semantics defined, examples work**
⚠️ **Properties not yet proved** - Good exercise for learning!

---

### File: `Imp/Examples.v`

#### What it Does

Provides concrete examples of expression evaluation using the small-step semantics.

#### Example Expressions

```coq
Definition ex1 : aexp := APlus (ANum 3) (ANum 4).
Definition ex2 : aexp := AMult (ANum 2) (ANum 5).
Definition ex3 : aexp := APlus (AMult (ANum 2) (ANum 3)) (ANum 4).
```

#### Example Proofs

```coq
(* 3 + 4 steps to 7 *)
Example ex1_steps : ex1 --> ANum 7.
Proof.
  apply ST_PlusConstConst.
Qed.

(* (2 * 3) + 4 multisteps to 10 *)
Example ex3_multisteps : multi ex3 (ANum 10).
Proof.
  unfold ex3.
  eapply multi_step. apply ST_Plus1. apply ST_MultConstConst.
  (* (2*3) + 4 --> 6 + 4 *)
  eapply multi_step. apply ST_PlusConstConst.
  (* 6 + 4 --> 10 *)
  apply multi_refl.
Qed.
```

#### Current Status
✅ **All examples work correctly**

---

## Langs Module

The Langs module explores correctness of automata and parsers.

### File: `Langs/SimpleDFA.v`

#### What it Proves

Correctness of a **deterministic finite automaton (DFA)** that accepts words with an **even number of 1s** (true symbols).

#### Key Definitions

1. **DFA Components**
```coq
Definition symbol := bool.  (* Alphabet: {false, true} *)
Definition word := list symbol.

Inductive state := Even | Odd.  (* Two states *)

Definition start : state := Even.  (* Initial state *)

Definition step (q : state) (a : symbol) : state :=
  match q, a with
  | Even, true => Odd   (* Even state sees 1 → go to Odd *)
  | Odd, true  => Even  (* Odd state sees 1 → go to Even *)
  | q', false  => q'    (* 0 doesn't change state *)
  end.
```

2. **Run Function**: Process entire word
```coq
Fixpoint run (q : state) (w : word) : state :=
  match w with
  | [] => q
  | a :: w' => run (step q a) w'
  end.
```

3. **Acceptance**
```coq
Definition accepts (w : word) : bool :=
  match run start w with
  | Even => true
  | Odd  => false
  end.
```

#### Correctness Specification

The DFA should accept exactly those words with an even number of trues:

```coq
Fixpoint count_true (w : word) : nat :=
  match w with
  | [] => 0
  | b :: w' => (if b then 1 else 0) + count_true w'
  end.

Definition even_trues (w : word) : Prop :=
  Nat.even (count_true w) = true.

Theorem accepts_correct :
  forall w,
    accepts w = true <-> even_trues w.
```

**Meaning**: The DFA accepts word `w` if and only if `w` has an even number of trues.

#### Proof Strategy

The key lemma `step_parity` relates the `run` function to the parity of true counts:

```coq
Lemma step_parity :
  forall q w,
    run q w =
    match q, Nat.even (count_true w) with
    | Even, true => Even
    | Even, false => Odd
    | Odd, true => Odd
    | Odd, false => Even
    end.
```

**Proof approach**: Induction on `w`, considering cases for the current state and the next symbol.

#### Current Status
⚠️ **Admitted** - Proofs left as exercises
- These are good practice for combining induction, case analysis, and arithmetic reasoning

---

### File: `Langs/SimpleParser.v`

#### What it Proves

**Soundness** of a stack-based checker for **balanced parentheses**.

#### Key Definitions

1. **Input**: Sequence of parentheses
```coq
Inductive token := LParen | RParen.
Definition input := list token.
```

2. **Balanced Predicate** (Relational specification)
```coq
Inductive balanced : input -> Prop :=
| bal_empty : balanced []
| bal_concat : forall s1 s2,
    balanced s1 -> balanced s2 -> balanced (s1 ++ s2)
| bal_wrap : forall s,
    balanced s -> balanced (LParen :: s ++ [RParen]).
```

**Meaning**: A sequence is balanced if:
- Empty is balanced
- Concatenation of balanced sequences is balanced
- Wrapping balanced sequence in `(` `)` is balanced

3. **Stack-Based Checker** (Executable algorithm)
```coq
Fixpoint check_aux (stk : nat) (s : input) : option nat :=
  match s with
  | [] => Some stk
  | LParen :: s' => check_aux (S stk) s'  (* Push *)
  | RParen :: s' =>
      match stk with
      | 0 => None                           (* Error: unmatched ) *)
      | S stk' => check_aux stk' s'         (* Pop *)
      end
  end.

Definition check (s : input) : bool :=
  match check_aux 0 s with
  | Some 0 => true  (* Ended with empty stack *)
  | _ => false
  end.
```

#### Correctness Theorem

```coq
Lemma check_sound :
  forall s,
    check s = true -> balanced s.
```

**Meaning**: If the checker accepts, then the input is balanced.

**Note**: This is soundness only, not completeness. For completeness, we'd need:
```coq
Lemma check_complete :
  forall s,
    balanced s -> check s = true.
```

#### Proof Strategy

The proof requires relating the inductive `balanced` predicate to the operational `check_aux` function. Key steps:
1. Prove properties about `check_aux` (e.g., stack depth bounds)
2. Show that `check_aux 0 s = Some 0` implies a decomposition of `s` into balanced parts
3. Use induction and the `balanced` constructors

#### Current Status
⚠️ **Admitted** - Proofs left as exercises
- Helper lemma `check_aux_stack_nonneg` is admitted
- Main theorem `check_sound` is admitted
- Good exercise for combining operational and relational reasoning

---

## Code Analysis and Issues

### Summary of Issues

| File | Status | Issues |
|------|--------|--------|
| `Basics/InductionLists.v` | ✅ Complete | None - all proofs finished |
| `Basics/Automation.v` | ✅ Complete | None - demonstrates automation |
| `Basics/InductionListsTest.v` | ✅ Complete | None - all tests pass |
| `Imp/Syntax.v` | ✅ Complete | None - pure definitions |
| `Imp/SmallStep.v` | ⚠️ Partial | Missing proofs of determinism, progress |
| `Imp/Examples.v` | ✅ Complete | None - examples work |
| `Langs/SimpleDFA.v` | ⚠️ Partial | Two lemmas admitted: `step_parity`, `accepts_correct` |
| `Langs/SimpleParser.v` | ⚠️ Partial | Two lemmas admitted: `check_aux_stack_nonneg`, `check_sound` |

### Detailed Issue Analysis

#### 1. `Langs/SimpleDFA.v` - Admitted Proofs

**Issue**: `step_parity` and `accepts_correct` are admitted.

**Why this matters**: These are the core correctness theorems for the DFA. Without them, we haven't actually verified that the DFA correctly accepts words with even numbers of trues.

**How to fix**: 
```coq
Lemma step_parity :
  forall q w,
    run q w =
    match q, Nat.even (count_true w) with
    | Even, true => Even
    | Even, false => Odd
    | Odd, true => Odd
    | Odd, false => Even
    end.
Proof.
  intros q w.
  induction w as [| a w' IH].
  - (* w = [] *)
    simpl. destruct q; reflexivity.
  - (* w = a :: w' *)
    simpl.
    destruct a; simpl.
    + (* a = true *)
      destruct q.
      * (* q = Even *)
        (* Use IH for Odd state *)
        (* Need to relate Nat.even (S n) to Nat.even n *)
        (* ... *)
      * (* q = Odd *)
        (* Similar *)
    + (* a = false *)
      destruct q; apply IH.
Qed.
```

**Difficulty**: Medium - requires understanding parity arithmetic

---

#### 2. `Langs/SimpleParser.v` - Admitted Proofs

**Issue**: `check_aux_stack_nonneg` and `check_sound` are admitted.

**Why this matters**: Without these proofs, we haven't verified that the parser is correct. The checker could be buggy.

**How to fix**:

First, the helper lemma:
```coq
Lemma check_aux_stack_nonneg :
  forall stk s stk',
    check_aux stk s = Some stk' -> stk' <= stk + length s.
Proof.
  intros stk s.
  generalize dependent stk.
  induction s as [| t s' IH]; intros stk stk' H.
  - (* s = [] *)
    simpl in H. injection H as H. subst. lia.
  - (* s = t :: s' *)
    simpl in H.
    destruct t.
    + (* LParen *)
      apply IH in H. simpl. lia.
    + (* RParen *)
      destruct stk.
      * discriminate.
      * apply IH in H. simpl. lia.
Qed.
```

For `check_sound`, the proof is more involved and requires a stronger induction principle.

**Difficulty**: Hard - requires careful invariant reasoning

---

#### 3. `Imp/SmallStep.v` - Missing Properties

**Issue**: No proofs of determinism, progress, or other standard properties.

**Why this matters**: These properties establish that the semantics is well-behaved.

**Standard theorems to add**:

```coq
(* Determinism *)
Theorem step_deterministic :
  forall a b c,
    a --> b ->
    a --> c ->
    b = c.
Proof.
  intros a b c Hb Hc.
  generalize dependent c.
  induction Hb; intros c Hc; inversion Hc; subst.
  - (* Both used ST_PlusConstConst *)
    reflexivity.
  - (* Contradiction: ST_PlusConstConst vs ST_Plus1 *)
    (* ANum doesn't step *)
  (* ... *)
Qed.

(* Values don't step *)
Lemma value_no_step :
  forall a b,
    is_value a ->
    a --> b ->
    False.
Proof.
  intros a b Hval Hstep.
  destruct a; try contradiction.
  inversion Hstep.
Qed.

(* Progress *)
Theorem progress :
  forall a,
    is_value a \/ exists b, a --> b.
Proof.
  induction a.
  - left. simpl. trivial.
  - (* APlus case *)
    right.
    destruct IHa1 as [Hv1 | [a1' Ha1']].
    + (* a1 is value *)
      destruct IHa2 as [Hv2 | [a2' Ha2']].
      * (* Both values *)
        destruct a1; try contradiction.
        destruct a2; try contradiction.
        exists (ANum (n + n0)).
        apply ST_PlusConstConst.
      * (* a2 steps *)
        destruct a1; try contradiction.
        exists (APlus (ANum n) a2').
        apply ST_Plus2. assumption.
    + (* a1 steps *)
      exists (APlus a1' a2).
      apply ST_Plus1. assumption.
  (* AMult similar *)
Qed.
```

**Difficulty**: Medium - standard metatheory

---

### What These Issues Mean

The admitted proofs are **exercise placeholders**. The codebase is a **teaching project** where:
- Core infrastructure is built
- Main theorems are stated
- Proof sketches are provided
- Actual proofs are left for the learner

This is a common pattern in interactive theorem proving courses!

---

## Learning Path

### For Absolute Beginners

1. **Start with**: `Basics/InductionLists.v`
   - Study the definitions of `app`, `rev`, `count`, `replicate`
   - Read through the completed proofs
   - Try to reproduce them without looking

2. **Next**: `Basics/InductionListsTest.v`
   - Run the `Compute` commands
   - Understand how theorems are applied

3. **Then**: `Basics/Automation.v`
   - Learn about hint databases
   - Understand the `crush` tactic
   - Try writing your own simple tactics

### For Intermediate Learners

4. **Study**: `Imp/Syntax.v` and `Imp/SmallStep.v`
   - Understand inductive syntax definitions
   - Learn about small-step semantics
   - Compare to big-step (evaluation) semantics

5. **Work through**: `Imp/Examples.v`
   - Trace the execution of `ex3_multisteps`
   - Try creating your own example expressions

6. **Attempt**: Complete the missing properties in `Imp/SmallStep.v`
   - Prove determinism
   - Prove progress
   - Prove that values don't step

### For Advanced Learners

7. **Tackle**: `Langs/SimpleDFA.v`
   - Prove `step_parity` by induction
   - Prove `accepts_correct` using `step_parity`
   - Think about extending to more complex DFAs

8. **Challenge**: `Langs/SimpleParser.v`
   - Prove `check_aux_stack_nonneg`
   - Prove `check_sound`
   - **Bonus**: Prove completeness (`balanced s -> check s = true`)

### Project Extensions

Once you've mastered the basics, try:

1. **Extend IMP**:
   - Add more operators (`AMod`, `ADiv`)
   - Add big-step semantics
   - Prove equivalence of small-step and big-step

2. **Complete IMP Semantics**:
   - Add semantics for commands (currently only expressions)
   - Prove properties of `CWhile` loops
   - Add program verification examples

3. **More Automata**:
   - DFA for other languages (e.g., strings ending in "01")
   - Non-deterministic finite automata (NFA)
   - Prove NFA to DFA conversion correct

4. **Parser Extensions**:
   - Parser for arithmetic expressions
   - Parser combinators
   - Prove soundness and completeness

---

## Resources

### Official Coq Resources

1. **Software Foundations** (https://softwarefoundations.cis.upenn.edu/)
   - Volume 1: Logical Foundations
   - Volume 2: Programming Language Foundations
   - The gold standard for learning Coq

2. **Coq Reference Manual** (https://coq.inria.fr/refman/)
   - Complete documentation of Coq
   - Tactic reference

3. **Coq'Art** (The Coq proof assistant: A Tutorial)
   - Comprehensive book by Bertot and Castéran
   - Covers both basics and advanced topics

### Community Resources

1. **Coq Discourse**: https://coq.zulipchat.com/
   - Active community forum
   - Ask questions, get help

2. **Proof General** or **VSCoq**:
   - IDE support for Coq
   - Essential for interactive development

3. **Coq Package Index** (https://coq.inria.fr/opam/www/)
   - Browse existing Coq libraries
   - Learn from others' code

### Related Topics

1. **Program Verification**:
   - Hoare Logic
   - Separation Logic
   - Concurrent program verification

2. **Dependent Types**:
   - Agda, Idris
   - Type-driven development

3. **Automated Theorem Proving**:
   - SMT solvers (Z3, CVC4)
   - SAT solvers

### Tips for Learning Coq

1. **Start Small**: Don't try to prove complex theorems right away
2. **Read Error Messages**: Coq's error messages are informative
3. **Use Tactics Incrementally**: Don't try to solve goals in one line
4. **Print Everything**: Use `Print`, `Check`, `About` to explore
5. **Practice Daily**: Proof skills need regular practice
6. **Don't Give Up**: Some proofs take time to "click"

---

## Conclusion

This project demonstrates key concepts in formal verification:
- **Functional correctness** (list operations)
- **Programming language semantics** (IMP language)
- **Automata theory** (DFA correctness)
- **Parser verification** (balanced parentheses)

The admitted proofs represent **learning opportunities**, not bugs. They're carefully chosen exercises that build skills in:
- Inductive reasoning
- Case analysis
- Invariant discovery
- Relating operational and relational specifications

Happy proving! 🎓
