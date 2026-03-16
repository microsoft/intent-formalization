(* Second completeness example — different input *)
module Test.ExtendedGCD2
#lang-pulse

open CLRS.Ch31.ExtendedGCD.Spec

(* No CLRS.Ch31.ExtendedGCD.Impl.fsti exists in autoclrs, so this remains a pure spec test. *)
let test_extended_gcd_48_18 () : Lemma (extended_gcd 48 18 == (| 6, -1, 3 |)) =
  assert_norm (extended_gcd 48 18 == (| 6, -1, 3 |))
