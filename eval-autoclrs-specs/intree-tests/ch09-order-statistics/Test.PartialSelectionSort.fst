module Test.PartialSelectionSort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.PartialSelectionSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

let select_spec_0 () : Lemma (PSSSpec.select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2) =
  assert_norm (PSSSpec.select_spec (Seq.seq_of_list [5; 2; 8]) 0 == 2)

```pulse
fn test_select ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 2;
  arr.(2sz) <- 8;

  let ctr = GR.alloc 0;
  let result = select arr 3sz 1sz ctr;
  // k=1: select_spec [5;2;8] 0 = 2 (0-indexed in spec, 1-indexed k)
  // result == Seq.index s_final (k-1) = s_final[0] = smallest = 2
  select_spec_0 ();
  assert (pure (result == 2));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
