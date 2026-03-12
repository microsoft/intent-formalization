module Test.BFS

open FStar.Mul
open FStar.Seq
open CLRS.Ch22.BFS.Spec

(* Graph: 3 vertices, edges: 0→1, 0→2
   Adjacency matrix (3×3 flat): adj[0*3+1]=1, adj[0*3+2]=1, rest=0 *)
let adj : seq int = seq_of_list [0; 1; 1; 0; 0; 0; 0; 0; 0]

(* === Soundness: edge checking === *)
let test_edge_01 () : Lemma (has_edge 3 adj 0 1 = true) =
  assert_norm (has_edge 3 adj 0 1 = true)

let test_edge_02 () : Lemma (has_edge 3 adj 0 2 = true) =
  assert_norm (has_edge 3 adj 0 2 = true)

let test_no_edge_10 () : Lemma (has_edge 3 adj 1 0 = false) =
  assert_norm (has_edge 3 adj 1 0 = false)

(* === Soundness: level 0 contains only source === *)
let test_level0 () : Lemma (
  Seq.index (level_0 3 0) 0 = true /\
  Seq.index (level_0 3 0) 1 = false /\
  Seq.index (level_0 3 0) 2 = false
) = assert_norm (
  Seq.index (level_0 3 0) 0 = true /\
  Seq.index (level_0 3 0) 1 = false /\
  Seq.index (level_0 3 0) 2 = false)

(* === Soundness: source is visited at level 0 === *)
let test_visited_source () : Lemma (is_visited 3 adj 0 0 0 = true) =
  assert_norm (is_visited 3 adj 0 0 0 = true)

(* === Soundness: vertex 1 is in frontier at level 1 === *)
let test_frontier_1 () : Lemma (is_frontier 3 adj 0 1 1 = true) =
  assert_norm (is_frontier 3 adj 0 1 1 = true)

(* === Completeness: vertex 1 not in frontier at level 0 === *)
[@@expect_failure]
let test_frontier_complete () : Lemma (is_frontier 3 adj 0 0 1 = true) =
  assert_norm (is_frontier 3 adj 0 0 1 = true)
