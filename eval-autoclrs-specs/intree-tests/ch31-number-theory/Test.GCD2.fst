(* Second completeness example — different input *)
module Test.GCD2
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.SizeT
open FStar.Mul
open CLRS.Ch31.GCD.Impl
open CLRS.Ch31.GCD.Spec

module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_gcd_15_10 (result: SZ.t) : Lemma
  (requires SZ.v result == gcd_spec 15 10)
  (ensures SZ.v result == 5)
= assert_norm (gcd_spec 15 10 == 5)
#pop-options

```pulse
fn test_gcd_15_10 ()
  requires emp
  returns _: unit
  ensures emp
{
  let ctr = GR.alloc #nat 0;
  let result = gcd_impl 15sz 10sz ctr;

  with cf. assert (GR.pts_to ctr cf);

  completeness_gcd_15_10 result;
  assert (pure (SZ.v result == 5));

  admit()
}
```
