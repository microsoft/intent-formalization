module Test.RabinKarp

open FStar.Mul
module Seq = FStar.Seq
open CLRS.Ch32.RabinKarp.Spec

(* === Soundness: pow function === *)
let test_pow_1 () : Lemma (pow 2 0 == 1) = ()
let test_pow_2 () : Lemma (pow 2 3 == 8) =
  assert_norm (pow 2 3 == 8)
let test_pow_3 () : Lemma (pow 10 2 == 100) =
  assert_norm (pow 10 2 == 100)

(* === Soundness: hash function on small sequence === *)
(* hash([1;2;3], d=10, q=7, 0, 3):
   = (10 * hash([1;2;3], 10, 7, 0, 2) + 3) % 7
   hash(0,2) = (10 * hash(0,1) + 2) % 7
   hash(0,1) = (10 * hash(0,0) + 1) % 7 = (10*0 + 1) % 7 = 1
   hash(0,2) = (10*1 + 2) % 7 = 12 % 7 = 5
   hash(0,3) = (10*5 + 3) % 7 = 53 % 7 = 4 *)
let seq123 : Seq.seq nat = Seq.seq_of_list [1; 2; 3]

let test_hash_sound () : Lemma (hash seq123 10 7 0 3 == 4) =
  assert_norm (hash seq123 10 7 0 3 == 4)

let test_hash_empty () : Lemma (hash seq123 10 7 0 0 == 0) = ()

(* === Soundness: pow_mod === *)
let test_pow_mod () : Lemma (pow_mod 10 2 7 == 2) =
  assert_norm (pow_mod 10 2 7 == 2)

(* === Completeness: wrong hash === *)
[@@expect_failure]
let test_hash_complete () : Lemma (hash seq123 10 7 0 3 == 5) =
  assert_norm (hash seq123 10 7 0 3 == 5)

(* === Completeness: wrong pow === *)
[@@expect_failure]
let test_pow_complete () : Lemma (pow 2 3 == 9) =
  assert_norm (pow 2 3 == 9)
