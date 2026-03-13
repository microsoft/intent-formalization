module Test.GCD

open FStar.Mul
open CLRS.Ch31.GCD.Spec

(* === Soundness tests: correct input/output pairs === *)
let test_sound_1 () : Lemma (gcd_spec 12 8 == 4) = ()
let test_sound_2 () : Lemma (gcd_spec 35 15 == 5) = ()
let test_sound_3 () : Lemma (gcd_spec 100 0 == 100) = ()


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_complete_1 (y:int) : Lemma
  (requires gcd_spec 12 8 == y)
  (ensures y == 4) =
  ()

let test_complete_2 (y:int) : Lemma
  (requires gcd_spec 35 15 == y)
  (ensures y == 5) =
  ()

let test_complete_3 (y:int) : Lemma
  (requires gcd_spec 100 0 == y)
  (ensures y == 100) =
  ()
