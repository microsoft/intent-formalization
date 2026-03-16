module Test.Stack
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

  push s 1;
  push s 2;
  push s 3;

  let popped = pop s;
  assert (pure (popped == 3));

  let top = peek s;
  assert (pure (top == 2));
}
```
