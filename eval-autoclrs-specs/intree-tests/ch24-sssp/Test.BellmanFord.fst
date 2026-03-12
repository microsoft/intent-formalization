module Test.BellmanFord

friend CLRS.Ch24.ShortestPath.Inf

open FStar.Mul
open FStar.Seq
open CLRS.Ch24.BellmanFord.Spec

(* 2-node graph: edge 0→1 with weight 3
   adj[0] = [0; 3], adj[1] = [inf; 0] *)
let adj2 : adj_matrix 2 =
  seq_of_list [seq_of_list [0; 3]; seq_of_list [1000000; 0]]

(* === Soundness: sp_dist_k with k=0, source=dest === *)
let test_self_dist () : Lemma (sp_dist_k adj2 0 0 0 == Some 0) =
  assert_norm (sp_dist_k adj2 0 0 0 == Some 0)

(* === Soundness: sp_dist_k with k=1, shortest path 0→1 = 3 === *)
let test_sp_k1 () : Lemma (sp_dist_k adj2 0 1 1 == Some 3) =
  assert_norm (sp_dist_k adj2 0 1 1 == Some 3)

(* === Soundness: no path with k=0 to different vertex === *)
let test_no_path () : Lemma (sp_dist_k adj2 0 1 0 == None) =
  assert_norm (sp_dist_k adj2 0 1 0 == None)

(* === Completeness: wrong distance === *)
[@@expect_failure]
let test_sp_complete () : Lemma (sp_dist_k adj2 0 1 1 == Some 4) =
  assert_norm (sp_dist_k adj2 0 1 1 == Some 4)
