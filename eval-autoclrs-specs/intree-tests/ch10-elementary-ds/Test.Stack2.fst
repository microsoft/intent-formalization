module Test.Stack2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch10.Stack.Impl

module SZ = FStar.SizeT

```pulse
fn test_stack_basic ()
  requires emp
  returns _: unit
  ensures exists* (s: stack int) (contents: Ghost.erased (list int)). stack_inv s contents
{
  let s = create_stack int 0 5sz;

  push s 10;
  push s 20;
  push s 30;

  let popped = pop s;
  assert (pure (popped == 30));

  let top = peek s;
  assert (pure (top == 20));
}
```
