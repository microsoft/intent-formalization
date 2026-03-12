module Test.RadixSort

open FStar.Seq
open FStar.Mul
open CLRS.Ch08.RadixSort.Spec

(* digit_sum computes the sum representation from digits *)
(* For k=123, base=10, bigD=3:
   digit(123, 10, 0) = 123 % 10 = 3
   digit(123, 10, 1) = (123/10) % 10 = 2
   digit(123, 10, 2) = (123/100) % 10 = 1
   digit_sum(123, 3, 10, 3) = 1*100 + 2*10 + 3*1 = 123 *)

(* === Soundness: digit_decomposition (k == digit_sum k bigD base bigD) === *)
let test_decomp () : Lemma (digit_sum 123 3 10 3 == 123) =
  digit_decomposition 123 3 10;
  assert_norm (digit_sum 123 3 10 3 == 123)

let test_decomp_2 () : Lemma (digit_sum 45 2 10 2 == 45) =
  digit_decomposition 45 2 10;
  assert_norm (digit_sum 45 2 10 2 == 45)

(* === Soundness: digit_sum with 0 digits is 0 === *)
let test_digit_sum_0 () : Lemma (digit_sum 123 3 10 0 == 0) =
  assert_norm (digit_sum 123 3 10 0 == 0)

(* === Completeness: wrong digit sum === *)
[@@expect_failure]
let test_decomp_complete () : Lemma (digit_sum 123 3 10 3 == 124) =
  assert_norm (digit_sum 123 3 10 3 == 124)
