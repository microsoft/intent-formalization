module Test.TopologicalSort

open FStar.Mul
open FStar.Seq
open CLRS.Ch22.TopologicalSort.Spec

(* Impl function: topological_sort (Pulse)
   Spec function tested: position_in_order (pure)
   Graph: 3 vertices, edges: 0->1, 1->2 (DAG)
   Valid topological order: [0; 1; 2] *)
let adj : seq int = seq_of_list [0; 1; 0; 0; 0; 1; 0; 0; 0]
let order : seq nat = seq_of_list [0; 1; 2]

(* === Completeness: position_in_order uniquely determines output === *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
let test_pos_0_complete (y:option nat) : Lemma
  (requires position_in_order order 0 == y)
  (ensures y == Some 0) =
  normalize_term_spec (position_in_order order 0)

let test_pos_1_complete (y:option nat) : Lemma
  (requires position_in_order order 1 == y)
  (ensures y == Some 1) =
  normalize_term_spec (position_in_order order 1)

let test_pos_2_complete (y:option nat) : Lemma
  (requires position_in_order order 2 == y)
  (ensures y == Some 2) =
  normalize_term_spec (position_in_order order 2)

let test_pos_missing_complete (y:option nat) : Lemma
  (requires position_in_order order 5 == y)
  (ensures y == None) =
  normalize_term_spec (position_in_order order 5)
#pop-options
