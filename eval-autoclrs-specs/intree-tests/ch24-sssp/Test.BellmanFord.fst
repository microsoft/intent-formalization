module Test.BellmanFord
#lang-pulse

friend CLRS.Ch24.ShortestPath.Inf

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch24.BellmanFord.Impl
open CLRS.Ch24.ShortestPath.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module V = Pulse.Lib.Vec

let bellman_ford_input_ok (sweights: Seq.seq int) : Lemma
  (requires
    Seq.length sweights == 4 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 3 /\
    Seq.index sweights 2 == SP.inf /\ Seq.index sweights 3 == 0)
  (ensures weights_in_range sweights 2)
=
  assert_norm (weights_in_range sweights 2)

let bellman_ford_complete (sweights sdist: Seq.seq int) (ok: bool) : Lemma
  (requires
    Seq.length sweights == 4 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 3 /\
    Seq.index sweights 2 == SP.inf /\ Seq.index sweights 3 == 0 /\
    Seq.length sdist == 2 /\
    Seq.index sdist 0 == 0)
  (ensures
    ok == true /\
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 == 3)
=
  admit()

```pulse
fn test_bellman_ford ()
  requires emp
  returns _: unit
  ensures emp
{
  let weights_v = V.alloc 0 4sz;
  V.to_array_pts_to weights_v;
  let weights = V.vec_to_array weights_v;
  rewrite (A.pts_to (V.vec_to_array weights_v) (Seq.create 4 0)) as (A.pts_to weights (Seq.create 4 0));
  weights.(1sz) <- 3;
  weights.(2sz) <- SP.inf;

  with sweights. assert (A.pts_to weights sweights);
  bellman_ford_input_ok sweights;

  let dist_v = V.alloc 0 2sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 2 0)) as (A.pts_to dist (Seq.create 2 0));

  let result = R.alloc false;
  let ctr = GR.alloc #nat 0;

  bellman_ford weights 2sz 0sz dist result ctr;

  with sdist. assert (A.pts_to dist sdist);
  with ok. assert (R.pts_to result ok);
  with cf. assert (GR.pts_to ctr cf);

  bellman_ford_complete sweights sdist ok;

  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let okv = R.(!result);

  assert (pure (okv == true));
  assert (pure (d0 == 0));
  assert (pure (d1 == 3));

  admit()
}
```