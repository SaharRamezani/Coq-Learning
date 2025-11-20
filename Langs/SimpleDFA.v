(** * A tiny DFA over bools *)

From Coq Require Import List Bool.
Import ListNotations.

Module SimpleDFA.

Definition symbol := bool.  (* false = 0, true = 1, say *)
Definition word := list symbol.

(* DFA that accepts words with an even number of [true] symbols. *)

Inductive state := Even | Odd.

Definition start : state := Even.

Definition step (q : state) (a : symbol) : state :=
  match q, a with
  | Even, true => Odd
  | Odd, true  => Even
  | q', false  => q'
  end.

Fixpoint run (q : state) (w : word) : state :=
  match w with
  | [] => q
  | a :: w' => run (step q a) w'
  end.

Definition accepts (w : word) : bool :=
  match run start w with
  | Even => true
  | Odd  => false
  end.

(* Relational definition: parity of trues *)

Fixpoint count_true (w : word) : nat :=
  match w with
  | [] => 0
  | b :: w' => (if b then 1 else 0) + count_true w'
  end.

Definition even_trues (w : word) : Prop :=
  Nat.even (count_true w) = true.

(* Main correctness lemma: DFA accepts iff parity is even *)

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
  (* Another good spot to demonstrate your Ltac automation. *)
Admitted.

Theorem accepts_correct :
  forall w,
    accepts w = true <-> even_trues w.
Proof.
  intro w.
  unfold accepts, even_trues.
  (* Use [step_parity] to connect [run start w] to parity. *)
Admitted.

End SimpleDFA.
