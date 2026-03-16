module Test.MinMax2
#lang-pulse

(* Second completeness example — different input *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.MinMax.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

let minmax_3sz_pre () : Lemma (ensures SZ.v 3sz > 0) =
  assert_norm (SZ.v 3sz > 0)

```pulse
fn test_find_minimum ()
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
  let min_val = find_minimum #_ arr #s0 3sz ctr #(hide 0);
  // Postcondition: min_val exists in array AND min_val <= all elements
  // For [7, 1, 4], min = 1
  assert (pure (min_val == 1));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_find_maximum ()
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
  let max_val = find_maximum #_ arr #s0 3sz ctr #(hide 0);
  // Postcondition: max_val exists in array AND max_val >= all elements
  // For [7, 1, 4], max = 7
  assert (pure (max_val == 7));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
