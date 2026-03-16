(* Second completeness example — different input *)
module Test.ModExpLR2
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch31.ModExpLR.Impl
open CLRS.Ch31.ModExp.Spec

module GR = Pulse.Lib.GhostReference

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_modexp_lr_3_5_13 (result: int) : Lemma
  (requires result == mod_exp_spec 3 5 13)
  (ensures result == 9)
= assert_norm (mod_exp_spec 3 5 13 == 9)
#pop-options

```pulse
fn test_modexp_lr_3_5_13 ()
  requires emp
  returns _: unit
  ensures emp
{
  let ctr = GR.alloc #nat 0;
  let result = mod_exp_lr_impl 3 5 13 ctr;

  with cf. assert (GR.pts_to ctr cf);

  completeness_modexp_lr_3_5_13 result;
  assert (pure (result == 9));

  admit()
}
```
