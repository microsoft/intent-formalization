(* Second completeness example — different input *)
module Test.Dijkstra3
#lang-pulse

friend CLRS.Ch24.ShortestPath.Inf

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch24.Dijkstra.Impl
open CLRS.Ch24.ShortestPath.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = CLRS.Ch24.ShortestPath.Spec
module V = Pulse.Lib.Vec

let dijkstra_input_ok (sweights: Seq.seq int) : Lemma
  (requires
    Seq.length sweights == 4 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 3 /\
    Seq.index sweights 2 == SP.inf /\ Seq.index sweights 3 == SP.inf)
  (ensures all_weights_non_negative sweights /\ weights_in_range sweights 2)
=
  assert_norm (all_weights_non_negative sweights /\ weights_in_range sweights 2)

#push-options "--fuel 16 --ifuel 8 --z3rlimit 1600"
let dijkstra_complete (sweights: Seq.seq int) (sdist: Seq.seq int) (spred: Seq.seq SZ.t) : Lemma
  (requires
    Seq.length sweights == 4 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 3 /\
    Seq.index sweights 2 == SP.inf /\ Seq.index sweights 3 == SP.inf /\
    Seq.length sdist == 2 /\
    (forall (v: nat). v < 2 ==> Seq.index sdist v == SP.sp_dist sweights 2 0 v) /\
    shortest_path_tree spred sweights 2 0)
  (ensures
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 == 3 /\
    Seq.index spred 0 == 0sz /\
    Seq.index spred 1 == 0sz)
 =
  assert_norm (
    SP.sp_dist sweights 2 0 0 == 0 /\
    SP.sp_dist sweights 2 0 1 == 3);
  assert (Seq.index sdist 0 == 0);
  assert (Seq.index sdist 1 == 3);
  assert (Seq.index spred 0 == 0sz);

  let p1 = SZ.v (Seq.index spred 1) in
  assert (p1 < 2 /\
    SP.sp_dist sweights 2 0 1 ==
      SP.sp_dist sweights 2 0 p1 + Seq.index sweights (p1 * 2 + 1));
  if p1 = 0 then ()
  else begin
    assert (p1 == 1);
    assert (Seq.index sweights (p1 * 2 + 1) == SP.inf);
    assert false
  end;
  assert (Seq.index spred 1 == 0sz)
#pop-options
```pulse
fn test_dijkstra3 ()
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
  weights.(3sz) <- SP.inf;

  with sweights. assert (A.pts_to weights sweights);
  dijkstra_input_ok sweights;

  let dist_v = V.alloc 0 2sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 2 0)) as (A.pts_to dist (Seq.create 2 0));

  let pred_v = V.alloc 0sz 2sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 2 0sz)) as (A.pts_to pred (Seq.create 2 0sz));

  let ctr = GR.alloc #nat 0;
  dijkstra weights 2sz 0sz dist pred ctr;

  with sdist. assert (A.pts_to dist sdist **
    pure (
      Seq.length sdist == 2 /\
      (forall (v: nat). v < 2 ==> Seq.index sdist v == SP.sp_dist sweights 2 0 v)));
  with spred. assert (A.pts_to pred spred **
    pure (shortest_path_tree spred sweights 2 0));
  with cf. assert (GR.pts_to ctr cf);

  dijkstra_complete sweights sdist spred;

  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let p0 = pred.(0sz);
  let p1 = pred.(1sz);

  assert (pure (d0 == 0));
  assert (pure (d1 == 3));
  assert (pure (p0 == 0sz));
  assert (pure (p1 == 0sz));

  admit()
}
```
