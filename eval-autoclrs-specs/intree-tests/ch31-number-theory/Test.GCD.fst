module Test.GCD

open FStar.Mul
open CLRS.Ch31.GCD.Spec

(* === Soundness tests: correct input/output pairs === *)
let test_sound_1 () : Lemma (gcd_spec 12 8 == 4) = ()
let test_sound_2 () : Lemma (gcd_spec 35 15 == 5) = ()
let test_sound_3 () : Lemma (gcd_spec 100 0 == 100) = ()

(* === Completeness tests: wrong outputs must fail === *)
[@@expect_failure]
let test_complete_1 () : Lemma (gcd_spec 12 8 == 3) = ()
[@@expect_failure]
let test_complete_2 () : Lemma (gcd_spec 35 15 == 7) = ()
[@@expect_failure]
let test_complete_3 () : Lemma (gcd_spec 100 0 == 50) = ()
