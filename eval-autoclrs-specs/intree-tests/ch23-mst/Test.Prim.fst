module Test.Prim

friend CLRS.Ch23.Prim.Spec

open FStar.List.Tot
open FStar.Seq
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

(* Simple 2-vertex graph: edge weight 5 between 0 and 1
   adj = [[0; 5]; [5; 0]] *)
let adj2 : adj_matrix = seq_of_list [seq_of_list [0; 5]; seq_of_list [5; 0]]

(* === Soundness: Prim on 2-vertex graph produces 1 edge === *)
let test_prim_count () : Lemma (List.Tot.length (pure_prim adj2 2 0) == 1) =
  assert_norm (List.Tot.length (pure_prim adj2 2 0) == 1)


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_prim_count_complete (y:int) : Lemma
  (requires List.Tot.length (pure_prim adj2 2 0) == y)
  (ensures y == 1) =
  assert_norm (List.Tot.length (pure_prim adj2 2 0) == 1)
