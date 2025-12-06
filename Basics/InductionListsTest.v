From Coq Require Import List Arith.
Import ListNotations.
Require Import InductionLists.

(* Import the module *)
Import InductionLists.InductionLists.

(* Test append *)
Compute app [1; 2; 3] [4; 5; 6].
(* Expected: [1; 2; 3; 4; 5; 6] *)

(* Test reverse *)
Compute rev [1; 2; 3; 4].
(* Expected: [4; 3; 2; 1] *)

(* Test count *)
Compute count 3 [1; 2; 3; 3; 4; 3].
(* Expected: 3 *)

(* Test replicate *)
Compute replicate 5 7.
(* Expected: [7; 7; 7; 7; 7] *)

(* Test count_replicate theorem *)
Example test_count_replicate : count 5 (replicate 10 5) = 10.
Proof. apply count_replicate. Qed.

(* Test rev_involutive theorem *)
Example test_rev_involutive : rev (rev [1; 2; 3]) = [1; 2; 3].
Proof. apply rev_involutive. Qed.
