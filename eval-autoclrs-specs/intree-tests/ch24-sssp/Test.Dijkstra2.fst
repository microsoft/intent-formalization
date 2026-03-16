(* Non-determinism test: this completeness check is expected to be unprovable *)
module Test.Dijkstra2
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
    Seq.length sweights == 16 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 1 /\ Seq.index sweights 2 == 1 /\ Seq.index sweights 3 == SP.inf /\
    Seq.index sweights 4 == SP.inf /\ Seq.index sweights 5 == 0 /\ Seq.index sweights 6 == SP.inf /\ Seq.index sweights 7 == 1 /\
    Seq.index sweights 8 == SP.inf /\ Seq.index sweights 9 == SP.inf /\ Seq.index sweights 10 == 0 /\ Seq.index sweights 11 == 1 /\
    Seq.index sweights 12 == SP.inf /\ Seq.index sweights 13 == SP.inf /\ Seq.index sweights 14 == SP.inf /\ Seq.index sweights 15 == 0)
  (ensures all_weights_non_negative sweights /\ weights_in_range sweights 4)
=
  assert_norm (all_weights_non_negative sweights /\ weights_in_range sweights 4)

#push-options "--fuel 16 --ifuel 8 --z3rlimit 1600"
let dijkstra_complete_nondet (sweights: Seq.seq int) (sdist: Seq.seq int) (spred: Seq.seq SZ.t) : Lemma
  (requires
    Seq.length sweights == 16 /\
    Seq.index sweights 0 == 0 /\ Seq.index sweights 1 == 1 /\ Seq.index sweights 2 == 1 /\ Seq.index sweights 3 == SP.inf /\
    Seq.index sweights 4 == SP.inf /\ Seq.index sweights 5 == 0 /\ Seq.index sweights 6 == SP.inf /\ Seq.index sweights 7 == 1 /\
    Seq.index sweights 8 == SP.inf /\ Seq.index sweights 9 == SP.inf /\ Seq.index sweights 10 == 0 /\ Seq.index sweights 11 == 1 /\
    Seq.index sweights 12 == SP.inf /\ Seq.index sweights 13 == SP.inf /\ Seq.index sweights 14 == SP.inf /\ Seq.index sweights 15 == 0 /\
    Seq.length sdist == 4 /\
    (forall (v: nat). v < 4 ==> Seq.index sdist v == SP.sp_dist sweights 4 0 v) /\
    shortest_path_tree spred sweights 4 0)
  (ensures
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 == 1 /\
    Seq.index sdist 2 == 1 /\
    Seq.index sdist 3 == 2 /\
    Seq.index spred 3 == 1sz)
= admit()
#pop-options

fn test_dijkstra2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let weights_v = V.alloc 0 16sz;
  V.to_array_pts_to weights_v;
  let weights = V.vec_to_array weights_v;
  rewrite (A.pts_to (V.vec_to_array weights_v) (Seq.create 16 0)) as (A.pts_to weights (Seq.create 16 0));
  weights.(1sz) <- 1;
  weights.(2sz) <- 1;
  weights.(3sz) <- SP.inf;
  weights.(4sz) <- SP.inf;
  weights.(6sz) <- SP.inf;
  weights.(7sz) <- 1;
  weights.(8sz) <- SP.inf;
  weights.(9sz) <- SP.inf;
  weights.(11sz) <- 1;
  weights.(12sz) <- SP.inf;
  weights.(13sz) <- SP.inf;
  weights.(14sz) <- SP.inf;

  with sweights. assert (A.pts_to weights sweights);
  dijkstra_input_ok sweights;

  let dist_v = V.alloc 0 4sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 4 0)) as (A.pts_to dist (Seq.create 4 0));

  let pred_v = V.alloc 0sz 4sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 4 0sz)) as (A.pts_to pred (Seq.create 4 0sz));

  let ctr = GR.alloc #nat 0;
  dijkstra weights 4sz 0sz dist pred ctr;

  with sdist. assert (A.pts_to dist sdist **
    pure (
      Seq.length sdist == 4 /\
      (forall (v: nat). v < 4 ==> Seq.index sdist v == SP.sp_dist sweights 4 0 v)));
  with spred. assert (A.pts_to pred spred **
    pure (shortest_path_tree spred sweights 4 0));
  with cf. assert (GR.pts_to ctr cf);

  dijkstra_complete_nondet sweights sdist spred;

  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);
  let d3 = dist.(3sz);
  let p3 = pred.(3sz);

  assert (pure (d0 == 0));
  assert (pure (d1 == 1));
  assert (pure (d2 == 1));
  assert (pure (d3 == 2));
  assert (pure (p3 == 1sz));

  admit()
}
