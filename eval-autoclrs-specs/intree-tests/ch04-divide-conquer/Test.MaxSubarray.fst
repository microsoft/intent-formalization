module Test.MaxSubarray

open FStar.Seq
module Seq = FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec

(* Simple case: all positive *)
let arr2 : Seq.seq int = Seq.seq_of_list [1; 2; 3]
let test_sound_2 () : Lemma (max_subarray_spec arr2 == 6) =
  assert_norm (max_subarray_spec arr2 == 6)

(* Single element *)
let arr3 : Seq.seq int = Seq.seq_of_list [5]
let test_sound_3 () : Lemma (max_subarray_spec arr3 == 5) =
  assert_norm (max_subarray_spec arr3 == 5)

(* Mixed positive/negative: [(-1); 3; (-2)] => max = 3 *)
let arr4 : Seq.seq int = Seq.seq_of_list [(-1); 3; (-2)]
let test_sound_4 () : Lemma (max_subarray_spec arr4 == 3) =
  assert_norm (max_subarray_spec arr4 == 3)

(* 5-element example: [-1; 4; -1; 2; -3] => max = 5 (subarray [4; -1; 2]) *)
let arr5 : Seq.seq int = Seq.seq_of_list [(-1); 4; (-1); 2; (-3)]
let test_sound_5 () : Lemma (max_subarray_spec arr5 == 5) =
  assert_norm (max_subarray_spec arr5 == 5)


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_complete_2 (y:int) : Lemma
  (requires max_subarray_spec arr2 == y)
  (ensures y == 6) =
  assert_norm (max_subarray_spec arr2 == 6)

let test_complete_3 (y:int) : Lemma
  (requires max_subarray_spec arr3 == y)
  (ensures y == 5) =
  assert_norm (max_subarray_spec arr3 == 5)

let test_complete_4 (y:int) : Lemma
  (requires max_subarray_spec arr4 == y)
  (ensures y == 3) =
  assert_norm (max_subarray_spec arr4 == 3)

let test_complete_5 (y:int) : Lemma
  (requires max_subarray_spec arr5 == y)
  (ensures y == 5) =
  assert_norm (max_subarray_spec arr5 == 5)
