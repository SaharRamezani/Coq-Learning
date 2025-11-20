# mini-verif-lab

Small Coq developments exploring foundational topics in formal verification:

- **Mechanized small-step semantics** for a toy imperative language (`Imp/`).
- **Verified functional programs** using induction (`Basics/`).
- **Basic parser and automaton correctness** over strings (`Langs/`).
- **Custom proof automation** using Ltac and the `auto`/`eauto` hint databases (`Basics/Automation.v`).

## Structure

- `Basics/InductionLists.v`  
  Inductive definitions and proofs about lists (reverse, append), including
  correctness of simple functional programs.

- `Basics/Automation.v`  
  Experiments with Ltac: custom tactics and hint databases that
  automate recurring proof patterns from the other files.

- `Imp/Syntax.v`  
  Syntax of arithmetic/boolean expressions and commands for a tiny IMP-like language.

- `Imp/SmallStep.v`  
  Small-step operational semantics for the IMP language, with properties such as
  determinism of the step relation and multi-step closure.

- `Imp/Examples.v`  
  Example programs and proofs of their behavior using the small-step semantics.

- `Langs/SimpleParser.v`  
  A simple hand-written parser over lists of tokens, with a soundness lemma.

- `Langs/SimpleDFA.v`  
  A tiny DFA over `bool` symbols, with correctness lemmas relating its
  executable acceptance function to a relational definition.
