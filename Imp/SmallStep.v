(** * Small-step semantics for arithmetic expressions *)

From Coq Require Import Arith.

(* Simple arithmetic expressions *)
Inductive aexp : Type :=
| ANum : nat -> aexp
| APlus : aexp -> aexp -> aexp
| AMult : aexp -> aexp -> aexp.

(* An expression is a value if it's just a number *)
Definition is_value (a : aexp) : Prop :=
  match a with
  | ANum _ => True
  | _ => False
  end.

(* Small-step reduction relation *)
Reserved Notation "a '-->' b" (at level 40).

Inductive step : aexp -> aexp -> Prop :=
| ST_PlusConstConst : forall n1 n2,
    APlus (ANum n1) (ANum n2) --> ANum (n1 + n2)
| ST_Plus1 : forall a1 a1' a2,
    a1 --> a1' ->
    APlus a1 a2 --> APlus a1' a2
| ST_Plus2 : forall n1 a2 a2',
    a2 --> a2' ->
    APlus (ANum n1) a2 --> APlus (ANum n1) a2'
| ST_MultConstConst : forall n1 n2,
    AMult (ANum n1) (ANum n2) --> ANum (n1 * n2)
| ST_Mult1 : forall a1 a1' a2,
    a1 --> a1' ->
    AMult a1 a2 --> AMult a1' a2
| ST_Mult2 : forall n1 a2 a2',
    a2 --> a2' ->
    AMult (ANum n1) a2 --> AMult (ANum n1) a2'
where "a '-->' b" := (step a b).

(* Multi-step relation *)
Inductive multi : aexp -> aexp -> Prop :=
| multi_refl : forall a,
    multi a a
| multi_step : forall a b c,
    a --> b ->
    multi b c ->
    multi a c.

Notation "a '-->*' b" := (multi a b) (at level 40).

(* Example: (2 + 3) * 4 reduces to 20 *)
Example test_multistep :
  multi (AMult (APlus (ANum 2) (ANum 3)) (ANum 4))
        (ANum 20).
Proof.
  eapply multi_step. apply ST_Mult1. apply ST_PlusConstConst.
  eapply multi_step. apply ST_MultConstConst.
  apply multi_refl.
Qed.

(* Example: 3 + 4 reduces to 7 *)
Example test_step_simple :
  APlus (ANum 3) (ANum 4) --> ANum 7.
Proof.
  apply ST_PlusConstConst.
Qed.
