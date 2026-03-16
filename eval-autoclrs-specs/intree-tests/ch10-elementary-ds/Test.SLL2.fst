module Test.SLL2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch10.SinglyLinkedList.Base
open CLRS.Ch10.SinglyLinkedList.Impl

```pulse
fn test_sll_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let hd : dlist = None;
  intro_is_dlist_nil hd;

  let hd = list_insert 30 hd;
  let hd = list_insert 20 hd;
  let hd = list_insert 10 hd;

  let found = list_search hd 20;
  assert (pure (found == true));

  let hd = list_delete hd 20;

  let missing = list_search hd 20;
  assert (pure (missing == false));

  let hd = list_delete hd 10;
  let hd = list_delete hd 30;
  elim_is_dlist_nil hd;
}
```
