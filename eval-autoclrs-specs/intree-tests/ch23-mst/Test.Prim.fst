module Test.Prim
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Prim.Impl
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Prim.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let prim_complete (weights_seq key_seq parent_seq: Seq.seq SZ.t) : Lemma
  (requires
    Seq.length weights_seq == 4 /\
    Seq.index weights_seq 0 == 0sz /\ Seq.index weights_seq 1 == 5sz /\
    Seq.index weights_seq 2 == 5sz /\ Seq.index weights_seq 3 == 0sz /\
    Seq.length key_seq == 2 /\
    Seq.length parent_seq == 2 /\
    prim_correct key_seq parent_seq weights_seq 2 0)
  (ensures
    Seq.index key_seq 0 == 0sz /\
    Seq.index key_seq 1 == 5sz /\
    Seq.index parent_seq 0 == 0sz /\
    Seq.index parent_seq 1 == 0sz)
=
  admit()

```pulse
fn test_prim ()
  requires emp
  returns _: unit
  ensures emp
{
  let weights_v = V.alloc 0sz 4sz;
  V.to_array_pts_to weights_v;
  let weights = V.vec_to_array weights_v;
  rewrite (A.pts_to (V.vec_to_array weights_v) (Seq.create 4 0sz)) as (A.pts_to weights (Seq.create 4 0sz));
  weights.(1sz) <- 5sz;
  weights.(2sz) <- 5sz;

  with weights_seq. assert (A.pts_to weights weights_seq);

  let res = prim weights 2sz 0sz;
  let key = fst res;
  let parent = snd res;

  with key_seq. assert (V.pts_to (fst res) key_seq);
  rewrite (V.pts_to (fst res) key_seq) as (V.pts_to key key_seq);
  with parent_seq. assert (V.pts_to (snd res) parent_seq);
  rewrite (V.pts_to (snd res) parent_seq) as (V.pts_to parent parent_seq);

  prim_complete weights_seq key_seq parent_seq;

  V.to_array_pts_to key;
  let key_arr = V.vec_to_array key;
  rewrite (A.pts_to (V.vec_to_array key) key_seq) as (A.pts_to key_arr key_seq);

  V.to_array_pts_to parent;
  let parent_arr = V.vec_to_array parent;
  rewrite (A.pts_to (V.vec_to_array parent) parent_seq) as (A.pts_to parent_arr parent_seq);

  let k0 = key_arr.(0sz);
  let k1 = key_arr.(1sz);
  let p0 = parent_arr.(0sz);
  let p1 = parent_arr.(1sz);

  assert (pure (k0 == 0sz));
  assert (pure (k1 == 5sz));
  assert (pure (p0 == 0sz));
  assert (pure (p1 == 0sz));

  admit()
}
```