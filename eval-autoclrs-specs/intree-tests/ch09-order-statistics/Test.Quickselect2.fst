module Test.Quickselect2
#lang-pulse

(* Second completeness example — different input *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch09.Quickselect.Impl
open CLRS.Ch09.PartialSelectionSort.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

let quickselect_pre () : Lemma (ensures SZ.v 3sz > 0 /\ SZ.v 0sz < SZ.v 3sz /\ SZ.v 2sz < SZ.v 3sz) =
  assert_norm (SZ.v 3sz > 0 /\ SZ.v 0sz < SZ.v 3sz /\ SZ.v 2sz < SZ.v 3sz)

let select_spec_0 () : Lemma (select_spec (Seq.seq_of_list [7; 1; 4]) 0 == 1) =
  assert_norm (select_spec (Seq.seq_of_list [7; 1; 4]) 0 == 1)
let select_spec_2 () : Lemma (select_spec (Seq.seq_of_list [7; 1; 4]) 2 == 7) =
  assert_norm (select_spec (Seq.seq_of_list [7; 1; 4]) 2 == 7)

```pulse
fn test_quickselect_min ()
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
  quickselect_pre ();

  let ctr = GR.alloc #nat 0;
  let result = quickselect arr #s0 3sz 0sz ctr #(hide 0);
  // Postcondition: result == select_spec s0 k = select_spec [7;1;4] 0 = 1
  select_spec_0 ();
  assert (pure (result == 1));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

```pulse
fn test_quickselect_max ()
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
  quickselect_pre ();

  let ctr = GR.alloc #nat 0;
  let result = quickselect arr #s0 3sz 2sz ctr #(hide 0);
  select_spec_2 ();
  assert (pure (result == 7));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
