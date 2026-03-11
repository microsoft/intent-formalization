module Test.PartialSelectionSort

open FStar.Seq
open CLRS.Ch09.PartialSelectionSort.Spec

(* select_spec(s, k) = kth smallest element = (pure_sort s)[k] *)

(* === Soundness: select_spec on [3; 1; 2] === *)
let s1 : seq int = seq_of_list [3; 1; 2]

let test_select_sound_1 () : Lemma (select_spec s1 0 == 1) =
  assert_norm (select_spec s1 0 == 1)

let test_select_sound_2 () : Lemma (select_spec s1 1 == 2) =
  assert_norm (select_spec s1 1 == 2)

let test_select_sound_3 () : Lemma (select_spec s1 2 == 3) =
  assert_norm (select_spec s1 2 == 3)

(* === Soundness: is_sorted on sorted result === *)
let test_sort_sound () : Lemma (is_sorted (pure_sort s1)) =
  assert_norm (is_sorted (pure_sort s1))

(* === Completeness: wrong selection === *)
[@@expect_failure]
let test_select_complete_1 () : Lemma (select_spec s1 0 == 2) =
  assert_norm (select_spec s1 0 == 2)

[@@expect_failure]
let test_select_complete_2 () : Lemma (select_spec s1 0 == 3) =
  assert_norm (select_spec s1 0 == 3)
