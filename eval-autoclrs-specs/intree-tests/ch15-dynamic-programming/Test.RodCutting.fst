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


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_complete_len1 (y:int) : Lemma
  (requires optimal_revenue prices 1 == y)
  (ensures y == 1) =
  assert_norm (optimal_revenue prices 1 == 1)

let test_complete_len2 (y:int) : Lemma
  (requires optimal_revenue prices 2 == y)
  (ensures y == 5) =
  assert_norm (optimal_revenue prices 2 == 5)

let test_complete_len3 (y:int) : Lemma
  (requires optimal_revenue prices 3 == y)
  (ensures y == 8) =
  assert_norm (optimal_revenue prices 3 == 8)

#push-options "--z3rlimit 100"
let test_complete_len4 (y:int) : Lemma
  (requires optimal_revenue prices 4 == y)
  (ensures y == 10) =
  assert_norm (optimal_revenue prices 4 == 10)
#pop-options
