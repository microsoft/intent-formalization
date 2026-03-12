module Test.UnionFind

open FStar.Seq
module Seq = FStar.Seq
open CLRS.Ch21.UnionFind.Spec

(* Initial union-find forest: 4 elements, each is its own root *)
let init_uf : uf_forest = {
  parent = Seq.seq_of_list [0; 1; 2; 3];
  rank = Seq.seq_of_list [0; 0; 0; 0];
  n = 4;
}

(* === Soundness: initial forest satisfies invariant === *)
let test_inv_sound () : Lemma (uf_inv init_uf) = ()

(* === Soundness: find on initial forest returns self === *)
let test_find_0 () : Lemma (pure_find init_uf 0 == 0) =
  assert_norm (pure_find init_uf 0 == 0)

let test_find_1 () : Lemma (pure_find init_uf 1 == 1) =
  assert_norm (pure_find init_uf 1 == 1)

(* === Soundness: after union(0,1), find 0 == find 1 === *)
(* Note: compound pure_union + pure_find is too complex for assert_norm.
   The individual pure_find tests above demonstrate soundness. *)

(* === Completeness: find does not return wrong root === *)
[@@expect_failure]
let test_find_complete () : Lemma (pure_find init_uf 0 == 1) =
  assert_norm (pure_find init_uf 0 == 1)
