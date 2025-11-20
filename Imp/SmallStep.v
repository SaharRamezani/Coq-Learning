(** * Small-step semantics for IMP *)

From Coq Require Import Strings.String Arith Bool.
From MiniVerif.Imp Require Import Syntax.

Module SmallStep.

Import Syntax.

(* Evaluation of arithmetic/boolean expressions in a state *)

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AVar x => st x
  | APlus a1 a2 => aeval st a1 + aeval st a2
  | AMinus a1 a2 => aeval st a1 - aeval st a2
  | AMult a1 a2 => aeval st a1 * aeval st a2
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BEq a1 a2 => Nat.eqb (aeval st a1) (aeval st a2)
  | BLe a1 a2 => Nat.leb (aeval st a1) (aeval st a2)
  | BNot b1 => negb (beval st b1)
  | BAnd b1 b2 => andb (beval st b1) (beval st b2)
  end.

(* Configurations *)
Definition config := (com * state)%type.

Reserved Notation "c1 '/' st1 '-->' c2 '/' st2"
  (at level 40, st1 at level 39, c2 at level 39).

Inductive step : config -> config -> Prop :=
| ST_Ass : forall st x a,
    (CAss x a, st) --> (CSkip, update st x (aeval st a))
| ST_Seq1 : forall st c2,
    (CSeq CSkip c2, st) --> (c2, st)
| ST_Seq2 : forall st st' c1 c1' c2,
    (c1, st) --> (c1', st') ->
    (CSeq c1 c2, st) --> (CSeq c1' c2, st')
| ST_IfTrue : forall st b c1 c2,
    beval st b = true ->
    (CIf b c1 c2, st) --> (c1, st)
| ST_IfFalse : forall st b c1 c2,
    beval st b = false ->
    (CIf b c1 c2, st) --> (c2, st)
| ST_While : forall st b c,
    (CWhile b c, st) --> (CIf b (CSeq c (CWhile b c)) CSkip, st)
where "c1 '/' st1 '-->' c2 '/' st2" := (step (c1, st1) (c2, st2)).

(* Multi-step closure *)

Inductive multi {X} (R : X -> X -> Prop) : X -> X -> Prop :=
| multi_refl : forall x, multi R x x
| multi_step : forall x y z,
    R x y -> multi R y z -> multi R x z.

Notation "R '**' " := (multi R) (at level 70).

Definition multistep := multi step.

Notation "cfg1 '==>*' cfg2" := (multistep cfg1 cfg2)
  (at level 40).

(* Determinism of single-step *)

Theorem step_deterministic :
  forall cfg cfg1 cfg2,
    step cfg cfg1 ->
    step cfg cfg2 ->
    cfg1 = cfg2.
Proof.
  intros [c st] [c1 st1] [c2 st2] H1 H2.
  generalize dependent c2; generalize dependent st2.
  induction H1; intros st2 c2 H2; inversion H2; subst; try reflexivity;
    try congruence.
  - (* Seq2 *)
    specialize (IHH1 _ _ H4). inversion IHH1; reflexivity.
  - (* Seq2, other direction *)
    specialize (IHH1 _ _ H4). inversion IHH1; reflexivity.
Qed.

End SmallStep.
