module Test.Huffman

open FStar.List.Tot
open CLRS.Ch16.Huffman.Spec

(* === Soundness: freq_of on leaves and internal nodes === *)
let l1 : htree = Leaf 0 5
let l2 : htree = Leaf 1 9

let test_freq_leaf () : Lemma (freq_of l1 == 5) = ()

(* === Soundness: merge two leaves === *)
let merged = merge l1 l2

let test_merge_freq () : Lemma (freq_of merged == 14) =
  assert_norm (freq_of merged == 14)

(* === Soundness: weighted path length === *)
(* WPL of single leaf at depth 0 = 0 *)
let test_wpl_leaf () : Lemma (weighted_path_length l1 == 0) =
  assert_norm (weighted_path_length l1 == 0)

(* WPL of merged: 5*1 + 9*1 = 14 *)
let test_wpl_merged () : Lemma (weighted_path_length merged == 14) =
  assert_norm (weighted_path_length merged == 14)

(* === Soundness: cost === *)
(* cost of merged: freq_of l1 + freq_of l2 = 5 + 9 = 14 *)
let test_cost_merged () : Lemma (cost merged == 14) =
  assert_norm (cost merged == 14)

(* === Soundness: WPL = cost theorem === *)
let test_wpl_cost () : Lemma (weighted_path_length merged == cost merged) =
  wpl_equals_cost merged

(* === Completeness: wrong frequency === *)
[@@expect_failure]
let test_freq_complete () : Lemma (freq_of merged == 13) =
  assert_norm (freq_of merged == 13)

(* === Completeness: wrong WPL === *)
[@@expect_failure]
let test_wpl_complete () : Lemma (weighted_path_length merged == 13) =
  assert_norm (weighted_path_length merged == 13)
