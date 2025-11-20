(** * Simple proof automation utilities *)

From Coq Require Import List Arith Lia.
Import ListNotations.

Module Automation.

(* Some generic lemmas to use with hint databases *)

Lemma plus_0_r : forall n, n + 0 = n.
Proof. intro n; lia. Qed.

Lemma plus_S_r : forall n m, n + S m = S (n + m).
Proof. intros; lia. Qed.

Hint Rewrite app_nil_r : list_rw.

Fixpoint app {A} (xs ys : list A) : list A :=
  match xs with
  | [] => ys
  | x :: xs' => x :: app xs' ys
  end.

Lemma app_nil_r : forall (A : Type) (xs : list A),
  app xs [] = xs.
Proof.
  intros; induction xs; simpl; congruence.
Qed.

(* A tiny “crush” tactic combining simplification and arithmetic *)

Ltac crush :=
  repeat (simpl in *; subst; try rewrite ?app_nil_r in *;
          try autorewrite with list_rw in *;
          try lia; try congruence).

(* Demonstration lemma that uses [crush] almost by itself *)

Lemma demo_arith_list :
  forall (xs : list nat),
    length (app xs []) + 0 = length xs.
Proof.
  intros xs.
  crush.
Qed.

End Automation.
