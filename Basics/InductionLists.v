(** * Induction over lists and simple verified functions *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Module InductionLists.

(* A standard append function *)

Fixpoint app {A} (xs ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: app xs' ys
  end.

Lemma app_nil_r : forall (A : Type) (xs : list A),
  app xs [] = xs.
Proof.
  intros A xs; induction xs; simpl; congruence.
Qed.

Lemma app_assoc : forall (A : Type) (xs ys zs : list A),
  app xs (app ys zs) = app (app xs ys) zs.
Proof.
  intros A xs ys zs; induction xs; simpl; congruence.
Qed.

(* Reverse and a classic correctness lemma *)

Fixpoint rev {A} (xs : list A) : list A :=
  match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]
  end.

Lemma rev_app_distr : forall (A : Type) (xs ys : list A),
  rev (app xs ys) = app (rev ys) (rev xs).
Proof.
  intros A xs ys; induction xs; simpl.
  - now rewrite app_nil_r.
  - rewrite IHxs, app_assoc; reflexivity.
Qed.

Lemma rev_involutive : forall (A : Type) (xs : list A),
  rev (rev xs) = xs.
Proof.
  intros A xs; induction xs; simpl.
  - reflexivity.
  - rewrite rev_app_distr, IHxs; simpl.
    now rewrite app_nil_r.
Qed.

(* A simple “program”: counting occurrences *)

Fixpoint count (x : nat) (xs : list nat) : nat :=
  match xs with
  | [] => 0
  | y :: ys => (if Nat.eqb x y then 1 else 0) + count x ys
  end.

Fixpoint replicate (n x : nat) : list nat :=
  match n with
  | 0 => []
  | S n' => x :: replicate n' x
  end.

Lemma count_replicate :
  forall n x,
    count x (replicate n x) = n.
Proof.
  induction n; intro x; simpl.
  - reflexivity.
  - rewrite Nat.eqb_refl, IHn; lia.
Qed.

End InductionLists.
