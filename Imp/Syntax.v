(** * Syntax for a toy IMP language *)

From Coq Require Import Strings.String Arith List.
Import ListNotations.

Module Syntax.

Definition var := string.

Inductive aexp : Type :=
| ANum  : nat -> aexp
| AVar  : var -> aexp
| APlus : aexp -> aexp -> aexp
| AMinus: aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp.

Inductive com : Type :=
| CSkip   : com
| CAss    : var -> aexp -> com
| CSeq    : com -> com -> com
| CIf     : bexp -> com -> com -> com
| CWhile  : bexp -> com -> com.

(* States as partial maps from variables to nat *)

Definition state := var -> nat.

Definition empty_state : state := fun _ => 0.

Definition update (st : state) (x : var) (n : nat) : state :=
  fun y => if String.eqb y x then n else st y.

End Syntax.
