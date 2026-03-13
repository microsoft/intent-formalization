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


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_pow_1_complete (y:int) : Lemma
  (requires pow 2 0 == y)
  (ensures y == 1) =
  ()

let test_pow_2_complete (y:int) : Lemma
  (requires pow 2 3 == y)
  (ensures y == 8) =
  assert_norm (pow 2 3 == 8)

let test_pow_3_complete (y:int) : Lemma
  (requires pow 10 2 == y)
  (ensures y == 100) =
  assert_norm (pow 10 2 == 100)

let test_hash_complete (y:int) : Lemma
  (requires hash seq123 10 7 0 3 == y)
  (ensures y == 4) =
  assert_norm (hash seq123 10 7 0 3 == 4)

let test_hash_empty_complete (y:int) : Lemma
  (requires hash seq123 10 7 0 0 == y)
  (ensures y == 0) =
  ()

let test_pow_mod_complete (y:int) : Lemma
  (requires pow_mod 10 2 7 == y)
  (ensures y == 2) =
  assert_norm (pow_mod 10 2 7 == 2)
