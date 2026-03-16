module Test.GrahamScan
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch33.GrahamScan.Impl
open CLRS.Ch33.GrahamScan.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_find_bottom (result: SZ.t) (sxs sys: Seq.seq int) : Lemma
  (requires Seq.length sxs == 3 /\
            Seq.length sys == 3 /\
            Seq.index sxs 0 == 0 /\ Seq.index sxs 1 == 1 /\ Seq.index sxs 2 == 2 /\
            Seq.index sys 0 == 2 /\ Seq.index sys 1 == 0 /\ Seq.index sys 2 == 1 /\
            SZ.v result == find_bottom_spec sxs sys)
  (ensures SZ.v result == 1)
= assert_norm (SZ.v result == 1)
#pop-options

```pulse
fn test_find_bottom ()
  requires emp
  returns _: unit
  ensures emp
{
  let vx = V.alloc #int 0 3sz;
  V.to_array_pts_to vx;
  let xs = V.vec_to_array vx;
  rewrite (A.pts_to (V.vec_to_array vx) (Seq.create #int 3 0))
       as (A.pts_to xs (Seq.create #int 3 0));
  xs.(0sz) <- 0;
  xs.(1sz) <- 1;
  xs.(2sz) <- 2;

  let vy = V.alloc #int 0 3sz;
  V.to_array_pts_to vy;
  let ys = V.vec_to_array vy;
  rewrite (A.pts_to (V.vec_to_array vy) (Seq.create #int 3 0))
       as (A.pts_to ys (Seq.create #int 3 0));
  ys.(0sz) <- 2;
  ys.(1sz) <- 0;
  ys.(2sz) <- 1;

  with sxs. assert (A.pts_to xs sxs);
  with sys. assert (A.pts_to ys sys);

  let result = find_bottom #1.0R xs ys 3sz;

  completeness_find_bottom result sxs sys;
  assert (pure (SZ.v result == 1));

  admit()
}
```
