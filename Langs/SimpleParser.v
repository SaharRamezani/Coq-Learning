(** * Simple parser: balanced parentheses *)

From Coq Require Import List Bool.
Import ListNotations.

Module SimpleParser.

Inductive token := LParen | RParen.

Definition input := list token.

(* An inductive “balanced” predicate *)

Inductive balanced : input -> Prop :=
| bal_empty : balanced []
| bal_concat : forall s1 s2,
    balanced s1 -> balanced s2 -> balanced (s1 ++ s2)
| bal_wrap : forall s,
    balanced s -> balanced (LParen :: s ++ [RParen]).

(* A simple stack-based checker *)

Fixpoint check_aux (stk : nat) (s : input) : option nat :=
  match s with
  | [] => Some stk
  | LParen :: s' => check_aux (S stk) s'
  | RParen :: s' =>
      match stk with
      | 0 => None
      | S stk' => check_aux stk' s'
      end
  end.

Definition check (s : input) : bool :=
  match check_aux 0 s with
  | Some 0 => true
  | _ => false
  end.

(* Soundness: if [check s = true] then [balanced s]. *)

Lemma check_aux_stack_nonneg :
  forall stk s stk',
    check_aux stk s = Some stk' -> stk' <= stk + length s.
Proof.
  (* You can fill this in with list/arith induction; left as an
     exercise or a place to use your Automation.v tactics. *)
Admitted.

Lemma check_sound :
  forall s,
    check s = true -> balanced s.
Proof.
  intros s H.
  unfold check in H.
  destruct (check_aux 0 s) as [stk|] eqn:Heq; try discriminate.
  destruct stk; [| discriminate].
  (* stk = 0, so the check passed *)
  (* Sketch: prove a more general lemma about [check_aux stk s = Some stk']
     implying that [s] can be decomposed into a sequence of balanced subparts,
     then instantiate with [stk = 0] and [stk' = 0]. *)
Admitted.

End SimpleParser.
