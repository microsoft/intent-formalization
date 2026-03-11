module Test.VertexCover

open FStar.Mul
open FStar.List.Tot
open FStar.Seq
open CLRS.Ch35.VertexCover.Spec

(* Triangle graph: 3 vertices, edges (0,1), (1,2), (0,2)
   adj (3×3 flat): adj[0*3+1]=1, adj[0*3+2]=1, adj[1*3+2]=1 *)
let adj : seq int = seq_of_list [0; 1; 1; 0; 0; 1; 0; 0; 0]

(* === Soundness: edge extraction === *)
let edges = extract_edges adj 3 0 1

let test_edges_count () : Lemma (List.Tot.length edges == 3) =
  assert_norm (List.Tot.length edges == 3)

(* === Soundness: edge_uses_vertex === *)
let test_edge_uses () : Lemma (
  edge_uses_vertex (0, 1) 0 = true /\
  edge_uses_vertex (0, 1) 1 = true /\
  edge_uses_vertex (0, 1) 2 = false
) = ()

(* === Soundness: cover that selects all vertices counts correctly === *)
let cover_all : cover_fn = fun v -> v < 3

let test_count () : Lemma (count_cover cover_all 3 == 3) =
  assert_norm (count_cover cover_all 3 == 3)

let test_count_0 () : Lemma (count_cover cover_all 0 == 0) =
  assert_norm (count_cover cover_all 0 == 0)

(* === Completeness: empty cover counts zero === *)
let cover_none : cover_fn = fun _ -> false

let test_count_none () : Lemma (count_cover cover_none 3 == 0) =
  assert_norm (count_cover cover_none 3 == 0)

(* === Completeness: wrong count fails === *)
[@@expect_failure]
let test_count_complete () : Lemma (count_cover cover_all 3 == 2) =
  assert_norm (count_cover cover_all 3 == 2)
