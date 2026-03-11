module Test.MergeSort

module Seq = FStar.Seq
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec
open CLRS.Ch02.MergeSort.Spec

(* === Soundness: seq_merge on small inputs === *)
let a1 : Seq.seq int = Seq.seq_of_list [1]
let a2 : Seq.seq int = Seq.seq_of_list [2]

let test_merge_sound_1 () : Lemma (seq_merge a1 a2 == Seq.seq_of_list [1; 2]) =
  assert_norm (seq_merge a1 a2 == Seq.seq_of_list [1; 2])

let test_merge_sound_2 () : Lemma (seq_merge a2 a1 == Seq.seq_of_list [1; 2]) =
  assert_norm (seq_merge a2 a1 == Seq.seq_of_list [1; 2])

(* === Soundness: empty merge === *)
let empty : Seq.seq int = Seq.empty
let test_merge_sound_3 () : Lemma (seq_merge empty a1 == a1) =
  assert_norm (seq_merge empty a1 == a1)

let test_merge_sound_4 () : Lemma (seq_merge a1 empty == a1) =
  assert_norm (seq_merge a1 empty == a1)

(* === Completeness: wrong merge result === *)
[@@expect_failure]
let test_merge_complete_1 () : Lemma (seq_merge a1 a2 == Seq.seq_of_list [2; 1]) =
  assert_norm (seq_merge a1 a2 == Seq.seq_of_list [2; 1])

[@@expect_failure]
let test_merge_complete_2 () : Lemma (seq_merge a2 a1 == Seq.seq_of_list [2; 1]) =
  assert_norm (seq_merge a2 a1 == Seq.seq_of_list [2; 1])
