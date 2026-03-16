module Test.ExtendedGCD
#lang-pulse

open CLRS.Ch31.ExtendedGCD.Spec

(* No CLRS.Ch31.ExtendedGCD.Impl.fsti exists in autoclrs, so this remains a pure spec test. *)
let test_extended_gcd_30_18 () : Lemma (extended_gcd 30 18 == (| 6, -1, 2 |)) =
  assert_norm (extended_gcd 30 18 == (| 6, -1, 2 |))
