module Test.Quicksort

friend CLRS.Ch07.Quicksort.Complexity

open CLRS.Ch07.Quicksort.Complexity

(* worst_case_comparisons(n) = n*(n-1)/2 *)

(* === Soundness === *)
let test_wc_sound_1 () : Lemma (worst_case_comparisons 5 == 10) =
  assert_norm (worst_case_comparisons 5 == 10)

let test_wc_sound_2 () : Lemma (worst_case_comparisons 3 == 3) =
  assert_norm (worst_case_comparisons 3 == 3)

let test_wc_sound_3 () : Lemma (worst_case_comparisons 0 == 0) = ()

let test_wc_sound_4 () : Lemma (worst_case_comparisons 1 == 0) =
  assert_norm (worst_case_comparisons 1 == 0)

(* === Soundness: quadratic bound === *)
open FStar.Mul
let test_quadratic_bound () : Lemma (worst_case_comparisons 5 <= 5 * 5) =
  assert_norm (worst_case_comparisons 5 <= 5 * 5)

(* === Completeness: wrong count === *)
[@@expect_failure]
let test_wc_complete_1 () : Lemma (worst_case_comparisons 5 == 9) =
  assert_norm (worst_case_comparisons 5 == 9)

[@@expect_failure]
let test_wc_complete_2 () : Lemma (worst_case_comparisons 5 == 11) =
  assert_norm (worst_case_comparisons 5 == 11)
