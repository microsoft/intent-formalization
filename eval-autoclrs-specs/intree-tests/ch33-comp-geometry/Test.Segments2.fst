(* Second completeness example — different input: non-intersecting parallel segments *)
module Test.Segments2
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch33.Segments.Impl
open CLRS.Ch33.Segments.Spec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_segments_no_intersect (result: bool) : Lemma
  (requires result == segments_intersect_spec 0 0 2 0 0 1 2 1)
  (ensures result == false)
= assert_norm (segments_intersect_spec 0 0 2 0 0 1 2 1 == false)
#pop-options

```pulse
fn test_segments_no_intersect ()
  requires emp
  returns _: unit
  ensures emp
{
  let result = segments_intersect 0 0 2 0 0 1 2 1;

  completeness_segments_no_intersect result;
  assert (pure (result == false));

  admit()
}
```
