module Test.ModExp

open FStar.Mul
open CLRS.Ch31.ModExp.Spec

(* === Soundness: correct modular exponentiation === *)
let test_sound_1 () : Lemma (mod_exp_spec 2 10 1000 == 24) =
  assert_norm (mod_exp_spec 2 10 1000 == 24)
let test_sound_2 () : Lemma (mod_exp_spec 3 5 7 == 5) =
  assert_norm (mod_exp_spec 3 5 7 == 5)
let test_sound_3 () : Lemma (mod_exp_spec 5 3 13 == 8) =
  assert_norm (mod_exp_spec 5 3 13 == 8)

(* === Completeness: wrong results must fail === *)
[@@expect_failure]
let test_complete_1 () : Lemma (mod_exp_spec 2 10 1000 == 25) =
  assert_norm (mod_exp_spec 2 10 1000 == 25)
[@@expect_failure]
let test_complete_2 () : Lemma (mod_exp_spec 3 5 7 == 6) =
  assert_norm (mod_exp_spec 3 5 7 == 6)
