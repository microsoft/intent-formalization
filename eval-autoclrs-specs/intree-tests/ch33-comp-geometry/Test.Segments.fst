module Test.Segments
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Mul
open CLRS.Ch33.Segments.Impl
open CLRS.Ch33.Segments.Spec

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_segments_intersect (result: bool) : Lemma
  (requires result == segments_intersect_spec 0 0 2 0 1 (-1) 1 1)
  (ensures result == true)
= assert_norm (segments_intersect_spec 0 0 2 0 1 (-1) 1 1 == true)
#pop-options

```pulse
fn test_segments_intersect ()
  requires emp
  returns _: unit
  ensures emp
{
  let result = segments_intersect 0 0 2 0 1 (-1) 1 1;

  completeness_segments_intersect result;
  assert (pure (result == true));

  admit()
}
```
