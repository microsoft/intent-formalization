module Test.Queue2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch10.Queue.Impl

module Q = CLRS.Ch10.Queue.Impl
module SZ = FStar.SizeT

```pulse
fn test_queue_basic ()
  requires emp
  returns _: unit
  ensures exists* (q: Q.queue int) (contents: Ghost.erased (list int)). Q.queue_inv q contents
{
  let q = Q.create_queue int 0 5sz;

  Q.enqueue q 10;
  Q.enqueue q 20;

  let first = Q.dequeue q;
  assert (pure (first == 10));

  let second = Q.dequeue q;
  assert (pure (second == 20));
}
```
