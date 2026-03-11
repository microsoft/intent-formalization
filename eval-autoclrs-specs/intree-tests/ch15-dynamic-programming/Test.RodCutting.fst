module Test.RodCutting

open FStar.Mul
open FStar.Seq
open CLRS.Ch15.RodCutting.Spec

(* CLRS example: prices = [1; 5; 8; 9; 10; 17; 17; 20; 24; 30] *)
let prices : seq nat = seq_of_list [1; 5; 8; 9; 10; 17; 17; 20; 24; 30]

(* === Soundness: optimal revenue for small rods === *)
let test_sound_len1 () : Lemma (optimal_revenue prices 1 == 1) =
  assert_norm (optimal_revenue prices 1 == 1)

let test_sound_len2 () : Lemma (optimal_revenue prices 2 == 5) =
  assert_norm (optimal_revenue prices 2 == 5)

let test_sound_len3 () : Lemma (optimal_revenue prices 3 == 8) =
  assert_norm (optimal_revenue prices 3 == 8)

let test_sound_len4 () : Lemma (optimal_revenue prices 4 == 10) =
  assert_norm (optimal_revenue prices 4 == 10)

(* === Completeness: wrong revenue must fail === *)
[@@expect_failure]
let test_complete_len2 () : Lemma (optimal_revenue prices 2 == 2) =
  assert_norm (optimal_revenue prices 2 == 2)

[@@expect_failure]
let test_complete_len4 () : Lemma (optimal_revenue prices 4 == 9) =
  assert_norm (optimal_revenue prices 4 == 9)
