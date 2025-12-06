# mini-verif-lab

Small Coq developments exploring foundational topics in formal verification:

- **Mechanized small-step semantics** for a toy imperative language (`Imp/`).
- **Verified functional programs** using induction (`Basics/`).
- **Basic parser and automaton correctness** over strings (`Langs/`).
- **Custom proof automation** using Ltac and the `auto`/`eauto` hint databases (`Basics/Automation.v`).

## 📚 Complete Guide

**New to Coq or want to understand this project in depth?** Check out the [**Complete Coq Guide**](COQ_GUIDE.md) which includes:
- Introduction to Coq and theorem proving
- Detailed explanation of how each file works
- What theorems are being proved and why
- Analysis of admitted proofs and how to complete them
- Learning path from beginner to advanced
- Resources and tips for mastering Coq

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

## Testing and Verification

### Checking Individual Files

To verify that a specific Coq file compiles and all proofs are valid:

```bash
coqc <filename>.v
```

For example:
```bash
coqc Basics/InductionLists.v
coqc Imp/SmallStep.v
```

### Running Tests

Some modules include separate test files. To run them:

```bash
coqc Basics/InductionListsTest.v
```

### Building the Entire Project

The project includes a Makefile for building all files at once:

```bash
make
```

This will:
- Compile all `.v` files in the correct dependency order
- Generate `.vo` (compiled object) files
- Report any errors or incomplete proofs

To clean the build artifacts:

```bash
make clean
```

### Interactive Development

To work with files interactively in an IDE (CoqIDE, Proof General, VSCode with Coq extension):

1. Open the `.v` file in your editor
2. Step through the file line by line
3. Observe proof states and goals
4. Verify that all proofs complete with `Qed` (not `Admitted`)

### Verifying Completeness

Check that no proofs are incomplete by searching for `Admitted`:

```bash
grep -r "Admitted" --include="*.v"
```

An empty result means all proofs are complete.
