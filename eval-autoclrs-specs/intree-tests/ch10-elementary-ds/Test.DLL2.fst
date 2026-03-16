module Test.DLL2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch10.DLL.Impl
module R = Pulse.Lib.Reference

#push-options "--fuel 16 --ifuel 8 --z3rlimit 800"
```pulse
fn test_dll_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let hd_ref = R.alloc #dptr None;
  let tl_ref = R.alloc #dptr None;
  dll_nil None None;

  list_insert hd_ref tl_ref 3;
  list_insert hd_ref tl_ref 4;

  let hd1 = R.(!hd_ref);
  let tl1 = R.(!tl_ref);
  assert (pts_to hd_ref hd1 ** pts_to tl_ref tl1 ** dll hd1 tl1 [4; 3]);
  let found = list_search hd1 tl1 4;
  assert (pure (found == true));

  let missing = list_search hd1 tl1 5;
  assert (pure (missing == false));

  list_delete hd_ref tl_ref 4;
  list_delete hd_ref tl_ref 3;

  with hd3 tl3 l3.
    assert (pts_to hd_ref hd3 ** pts_to tl_ref tl3 ** dll hd3 tl3 l3);
  drop_ (dll hd3 tl3 l3);
  R.free hd_ref;
  R.free tl_ref;
}
```
#pop-options
