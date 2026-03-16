module Test.GCD
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Mul
open CLRS.Ch31.GCD.Impl
open CLRS.Ch31.GCD.Spec

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_gcd_12_8 (result: SZ.t) : Lemma
  (requires SZ.v result == gcd_spec 12 8)
  (ensures SZ.v result == 4)
= assert_norm (gcd_spec 12 8 == 4)
#pop-options

```pulse
fn test_gcd_12_8 ()
  requires emp
  returns _: unit
  ensures emp
{
  let ctr = GR.alloc #nat 0;
  let result = gcd_impl 12sz 8sz ctr;

  with cf. assert (GR.pts_to ctr cf);

  completeness_gcd_12_8 result;
  assert (pure (SZ.v result == 4));

  admit()
}
```
