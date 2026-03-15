(* Non-determinism test: this completeness check is expected to be unprovable *)
module Test.DFS2
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.DFS.Impl
open CLRS.Ch22.DFS.Spec
open CLRS.Ch22.Graph.Common

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_dfs_fork
  (sadj scolor sd sf spred: Seq.seq int)
  : Lemma
    (requires
      Seq.length sadj == 9 /\
      Seq.index sadj 0 == 0 /\ Seq.index sadj 1 == 1 /\ Seq.index sadj 2 == 1 /\
      Seq.index sadj 3 == 0 /\ Seq.index sadj 4 == 0 /\ Seq.index sadj 5 == 0 /\
      Seq.index sadj 6 == 0 /\ Seq.index sadj 7 == 0 /\ Seq.index sadj 8 == 0 /\
      Seq.length scolor == 3 /\
      Seq.length sd == 3 /\
      Seq.length sf == 3 /\
      Seq.length spred == 3 /\
      (forall (u: nat). u < 3 ==> Seq.index scolor u == 2) /\
      (forall (u: nat). u < 3 ==> Seq.index sd u > 0) /\
      (forall (u: nat). u < 3 ==> Seq.index sf u > 0) /\
      (forall (u: nat). u < 3 ==> Seq.index sd u < Seq.index sf u) /\
      pred_edge_ok sadj 3 scolor sd spred)
    (ensures Seq.index sd 1 == 2)
= admit()
#pop-options

fn test_dfs2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let adj_v = V.alloc 0 9sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 9 0)) as (A.pts_to adj (Seq.create 9 0));
  adj.(1sz) <- 1;
  adj.(2sz) <- 1;

  with s0. assert (A.pts_to adj s0);

  let color_v = V.alloc 0 3sz;
  V.to_array_pts_to color_v;
  let color = V.vec_to_array color_v;
  rewrite (A.pts_to (V.vec_to_array color_v) (Seq.create 3 0)) as (A.pts_to color (Seq.create 3 0));

  let d_v = V.alloc 0 3sz;
  V.to_array_pts_to d_v;
  let d = V.vec_to_array d_v;
  rewrite (A.pts_to (V.vec_to_array d_v) (Seq.create 3 0)) as (A.pts_to d (Seq.create 3 0));

  let f_v = V.alloc 0 3sz;
  V.to_array_pts_to f_v;
  let f = V.vec_to_array f_v;
  rewrite (A.pts_to (V.vec_to_array f_v) (Seq.create 3 0)) as (A.pts_to f (Seq.create 3 0));

  let pred_v = V.alloc 0 3sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 3 0)) as (A.pts_to pred (Seq.create 3 0));

  let stack_v = V.alloc 0sz 3sz;
  V.to_array_pts_to stack_v;
  let stack_data = V.vec_to_array stack_v;
  rewrite (A.pts_to (V.vec_to_array stack_v) (Seq.create 3 0sz)) as (A.pts_to stack_data (Seq.create 3 0sz));

  let scan_v = V.alloc 0sz 3sz;
  V.to_array_pts_to scan_v;
  let scan_idx = V.vec_to_array scan_v;
  rewrite (A.pts_to (V.vec_to_array scan_v) (Seq.create 3 0sz)) as (A.pts_to scan_idx (Seq.create 3 0sz));

  let ctr = GR.alloc #nat 0;
  stack_dfs adj 3sz color d f pred stack_data scan_idx ctr;

  with scolor sd sf spred sstack sscan cf.
    assert (A.pts_to adj s0 **
            A.pts_to color scolor **
            A.pts_to d sd **
            A.pts_to f sf **
            A.pts_to pred spred **
            A.pts_to stack_data sstack **
            A.pts_to scan_idx sscan **
            GR.pts_to ctr cf **
            pure (
              Seq.length scolor == 3 /\
              Seq.length sd == 3 /\
              Seq.length sf == 3 /\
              Seq.length spred == 3 /\
              (forall (u: nat). u < 3 ==> Seq.index scolor u == 2) /\
              (forall (u: nat). u < 3 ==> Seq.index sd u > 0) /\
              (forall (u: nat). u < 3 ==> Seq.index sf u > 0) /\
              (forall (u: nat). u < 3 ==> Seq.index sd u < Seq.index sf u) /\
              pred_edge_ok s0 3 scolor sd spred));

  completeness_dfs_fork s0 scolor sd sf spred;

  let d1 = d.(1sz);
  assert (pure (d1 == 2));

  admit()
}
