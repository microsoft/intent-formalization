module Test.Kruskal

open FStar.List.Tot
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec

(* === Soundness: sort_edges produces sorted list === *)
let e1 : edge = { u = 0; v = 1; w = 3 }
let e2 : edge = { u = 1; v = 2; w = 1 }
let e3 : edge = { u = 0; v = 2; w = 2 }

let test_sorted () : Lemma (is_sorted_by_weight (sort_edges [e1; e2; e3]) = true) =
  assert_norm (is_sorted_by_weight (sort_edges [e1; e2; e3]) = true)

(* === Soundness: kruskal_step adds non-cycle edge === *)
let test_step_adds () : Lemma (
  length (kruskal_step e2 [] 3) == 1
) = assert_norm (length (kruskal_step e2 [] 3) == 1)

(* === Soundness: pure_kruskal on 3-vertex graph produces 2 edges (spanning tree) === *)
let g : graph = { n = 3; edges = [e1; e2; e3] }

let test_kruskal_count () : Lemma (length (pure_kruskal g) == 2) =
  assert_norm (length (pure_kruskal g) == 2)

(* === Completeness: not 3 edges for 3-vertex graph === *)
[@@expect_failure]
let test_kruskal_complete () : Lemma (length (pure_kruskal g) == 3) =
  assert_norm (length (pure_kruskal g) == 3)
