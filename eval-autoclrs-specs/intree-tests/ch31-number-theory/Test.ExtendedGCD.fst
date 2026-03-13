module Test.ExtendedGCD

open FStar.Mul
open CLRS.Ch31.ExtendedGCD.Spec

(* extended_gcd(a, b) returns (| d, x, y |) where d = gcd(a,b), a*x + b*y = d *)

(* === Soundness: gcd(30, 18) = 6 === *)
let test_egcd_sound_1 () : Lemma (extended_gcd 30 18 == (| 6, -1, 2 |)) =
  assert_norm (extended_gcd 30 18 == (| 6, -1, 2 |))

(* === Soundness: gcd(35, 15) = 5, 35*1 + 15*(-2) = 5 === *)
let test_egcd_sound_2 () : Lemma (extended_gcd 35 15 == (| 5, 1, -2 |)) =
  assert_norm (extended_gcd 35 15 == (| 5, 1, -2 |))

(* === Soundness: gcd(a, 0) = a with coefficients (1, 0) === *)
let test_egcd_sound_3 () : Lemma (extended_gcd 7 0 == (| 7, 1, 0 |)) =
  assert_norm (extended_gcd 7 0 == (| 7, 1, 0 |))

(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_egcd_complete_1 (d:nat) (x:int) (z:int) : Lemma
  (requires extended_gcd 30 18 == (| d, x, z |))
  (ensures d == 6 /\ x == -1 /\ z == 2) =
  assert_norm (extended_gcd 30 18 == (| 6, -1, 2 |))

let test_egcd_complete_2 (d:nat) (x:int) (z:int) : Lemma
  (requires extended_gcd 35 15 == (| d, x, z |))
  (ensures d == 5 /\ x == 1 /\ z == -2) =
  assert_norm (extended_gcd 35 15 == (| 5, 1, -2 |))

let test_egcd_complete_3 (d:nat) (x:int) (z:int) : Lemma
  (requires extended_gcd 7 0 == (| d, x, z |))
  (ensures d == 7 /\ x == 1 /\ z == 0) =
  assert_norm (extended_gcd 7 0 == (| 7, 1, 0 |))
