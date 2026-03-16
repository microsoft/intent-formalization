module Test.DLL
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch10.DLL.Impl
module R = Pulse.Lib.Reference

```pulse
fn test_dll_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let hd_ref = R.alloc #dptr None;
  let tl_ref = R.alloc #dptr None;
  dll_nil None None;

  list_insert hd_ref tl_ref 1;
  list_insert hd_ref tl_ref 2;

  let hd1 = R.(!hd_ref);
  let tl1 = R.(!tl_ref);
  let found = list_search hd1 tl1 1;
  assert (pure (found == true));

  list_delete hd_ref tl_ref 1;

  let hd2 = R.(!hd_ref);
  let tl2 = R.(!tl_ref);
  let missing = list_search hd2 tl2 1;
  assert (pure (missing == false));

  list_delete hd_ref tl_ref 2;

  with hd3 tl3 l3.
    assert (pts_to hd_ref hd3 ** pts_to tl_ref tl3 ** dll hd3 tl3 l3);
  drop_ (dll hd3 tl3 l3);
  R.free hd_ref;
  R.free tl_ref;
}
```
