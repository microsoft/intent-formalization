module Test.SLL
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

  let hd = list_insert 3 hd;
  let hd = list_insert 2 hd;
  let hd = list_insert 1 hd;

  let found = list_search hd 2;
  assert (pure (found == true));

  let hd = list_delete hd 2;

  let missing = list_search hd 2;
  assert (pure (missing == false));

  let hd = list_delete hd 1;
  let hd = list_delete hd 3;
  elim_is_dlist_nil hd;
}
```
