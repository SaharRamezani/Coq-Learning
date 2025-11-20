(** * Example IMP programs and their behavior *)

From Coq Require Import Strings.String Arith.
From MiniVerif.Imp Require Import Syntax SmallStep.

Module Examples.

Import Syntax SmallStep.

(* Program: x := x + 1 *)

Definition inc (x : var) : com :=
  CAss x (APlus (AVar x) (ANum 1)).

Lemma inc_correct :
  forall st x,
    let st' := snd (CSkip, update st x (aeval st (APlus (AVar x) (ANum 1)))) in
    (inc x, st) --> (CSkip, update st x (st x + 1)).
Proof.
  intros st x; simpl.
  econstructor.
Qed.

(* A small while-loop: decrement x until zero *)

Definition dec_to_zero (x : var) : com :=
  CWhile (BLe (ANum 1) (AVar x))
    (CAss x (AMinus (AVar x) (ANum 1))).

(* You can then prove properties like:
   starting in a state where st x = n, after
   some number of steps the loop terminates
   with x = 0. (Sketch; you can fill it out.) *)

End Examples.
