module Test.BucketSort

open FStar.List.Tot
open CLRS.Ch08.BucketSort.Spec

(* === Soundness: sorted predicate on sorted list === *)
let test_sorted_sound () : Lemma (sorted [1; 2; 3; 4; 5]) = ()

(* === Soundness: insertion_sort sorts correctly === *)
let test_isort_sound () : Lemma (insertion_sort [3; 1; 2] == [1; 2; 3]) =
  assert_norm (insertion_sort [3; 1; 2] == [1; 2; 3])

(* === Soundness: insert into sorted list === *)
let test_insert_sound () : Lemma (insert 2 [1; 3; 5] == [1; 2; 3; 5]) =
  assert_norm (insert 2 [1; 3; 5] == [1; 2; 3; 5])

(* === Soundness: in_range predicate === *)
let test_in_range () : Lemma (in_range [1; 2; 3] 0 5) = ()

(* === Soundness: bucket_index computation === *)
let test_bucket_idx () : Lemma (bucket_index 5 0 10 5 == 2) =
  assert_norm (bucket_index 5 0 10 5 == 2)

(* === Completeness: unsorted list is NOT sorted === *)
[@@expect_failure]
let test_sorted_complete () : Lemma (sorted [3; 1; 2]) = ()

(* === Completeness: wrong sort result === *)
[@@expect_failure]
let test_isort_complete () : Lemma (insertion_sort [3; 1; 2] == [1; 3; 2]) =
  assert_norm (insertion_sort [3; 1; 2] == [1; 3; 2])
