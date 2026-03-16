module Test.SimultaneousMinMax2
#lang-pulse

(* Second completeness example — different input *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.SimultaneousMinMax.Impl
open CLRS.Ch09.SimultaneousMinMax.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

let minmax_3sz_pre () : Lemma (ensures SZ.v 3sz >= 1) =
  assert_norm (SZ.v 3sz >= 1)

```pulse
fn test_find_minmax ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  assert (pure (A.length arr == SZ.v 3sz));
  arr.(0sz) <- 7;
  arr.(1sz) <- 1;
  arr.(2sz) <- 4;

  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;
  assert (pure (Seq.length s0 == SZ.v 3sz));
  assert (pure (A.length arr == SZ.v 3sz));
  minmax_3sz_pre ();

  let ctr = GR.alloc #nat 0;
  let result = find_minmax #_ arr #s0 3sz ctr #(hide 0);
  assert (pure (result.min_val == 1));
  assert (pure (result.max_val == 7));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_find_minmax_pairs ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  assert (pure (A.length arr == SZ.v 3sz));
  arr.(0sz) <- 7;
  arr.(1sz) <- 1;
  arr.(2sz) <- 4;

  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;
  assert (pure (Seq.length s0 == SZ.v 3sz));
  assert (pure (A.length arr == SZ.v 3sz));
  minmax_3sz_pre ();

  let ctr = GR.alloc #nat 0;
  let result = find_minmax_pairs #_ arr #s0 3sz ctr #(hide 0);
  assert (pure (result.min_val == 1));
  assert (pure (result.max_val == 7));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
