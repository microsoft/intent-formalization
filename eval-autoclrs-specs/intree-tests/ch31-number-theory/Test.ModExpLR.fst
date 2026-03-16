module Test.ModExpLR
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExpLR.Impl
open CLRS.Ch31.ModExp.Spec

module GR = Pulse.Lib.GhostReference

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_modexp_lr_2_10_1000 (result: int) : Lemma
  (requires result == mod_exp_spec 2 10 1000)
  (ensures result == 24)
= assert_norm (mod_exp_spec 2 10 1000 == 24)
#pop-options

```pulse
fn test_modexp_lr_2_10_1000 ()
  requires emp
  returns _: unit
  ensures emp
{
  let ctr = GR.alloc #nat 0;
  let result = mod_exp_lr_impl 2 10 1000 ctr;

  with cf. assert (GR.pts_to ctr cf);

  completeness_modexp_lr_2_10_1000 result;
  assert (pure (result == 24));

  admit()
}
```
