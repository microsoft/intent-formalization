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


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_wc_complete_1 (y:int) : Lemma
  (requires worst_case_comparisons 5 == y)
  (ensures y == 10) =
  assert_norm (worst_case_comparisons 5 == 10)

let test_wc_complete_2 (y:int) : Lemma
  (requires worst_case_comparisons 3 == y)
  (ensures y == 3) =
  assert_norm (worst_case_comparisons 3 == 3)

let test_wc_complete_3 (y:int) : Lemma
  (requires worst_case_comparisons 0 == y)
  (ensures y == 0) =
  ()

let test_wc_complete_4 (y:int) : Lemma
  (requires worst_case_comparisons 1 == y)
  (ensures y == 0) =
  assert_norm (worst_case_comparisons 1 == 0)
