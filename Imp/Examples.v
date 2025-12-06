(** * Examples of arithmetic expression evaluation *)

From Coq Require Import Arith.
From MiniVerif.Imp Require Import SmallStep.

(* Some example expressions *)

Definition ex1 : aexp := APlus (ANum 3) (ANum 4).
Definition ex2 : aexp := AMult (ANum 2) (ANum 5).
Definition ex3 : aexp := APlus (AMult (ANum 2) (ANum 3)) (ANum 4).

(* Example: 3 + 4 steps to 7 *)
Example ex1_steps : ex1 --> ANum 7.
Proof.
  apply ST_PlusConstConst.
Qed.

(* Example: 2 * 5 steps to 10 *)
Example ex2_steps : ex2 --> ANum 10.
Proof.
  apply ST_MultConstConst.
Qed.

(* Example: (2 * 3) + 4 multisteps to 10 *)
Example ex3_multisteps : multi ex3 (ANum 10).
Proof.
  unfold ex3.
  eapply multi_step. apply ST_Plus1. apply ST_MultConstConst.
  eapply multi_step. apply ST_PlusConstConst.
  apply multi_refl.
Qed.
