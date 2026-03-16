(* Second completeness example — different input *)
module Test.FloydWarshall2
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch25.FloydWarshall.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module FW = CLRS.Ch25.FloydWarshall.Spec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"

let completeness_fw_2 (contents0 contents: Seq.seq int) : Lemma
  (requires
    Seq.length contents0 == 4 /\
    Seq.index contents0 0 == 0 /\
    Seq.index contents0 1 == 3 /\
    Seq.index contents0 2 == FW.inf /\
    Seq.index contents0 3 == 0 /\
    contents == FW.fw_outer contents0 2 0)
  (ensures
    Seq.index contents 0 == 0 /\
    Seq.index contents 1 == 3 /\
    Seq.index contents 2 == FW.inf /\
    Seq.index contents 3 == 0)
= assert_norm (
    Seq.index (FW.fw_outer contents0 2 0) 0 == 0 /\
    Seq.index (FW.fw_outer contents0 2 0) 1 == 3 /\
    Seq.index (FW.fw_outer contents0 2 0) 2 == FW.inf /\
    Seq.index (FW.fw_outer contents0 2 0) 3 == 0);
  assert (Seq.index contents 0 == 0);
  assert (Seq.index contents 1 == 3);
  assert (Seq.index contents 2 == FW.inf);
  assert (Seq.index contents 3 == 0)

#pop-options

fn test_floyd_warshall2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 4sz;
  V.to_array_pts_to v;
  let dist = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 4 0)) as (A.pts_to dist (Seq.create 4 0));
  dist.(0sz) <- 0;
  dist.(1sz) <- 3;
  dist.(2sz) <- FW.inf;
  dist.(3sz) <- 0;

  with contents0. assert (A.pts_to dist contents0);

  let ctr = GR.alloc #nat 0;
  floyd_warshall dist 2sz ctr;

  with contents. assert (A.pts_to dist contents);
  completeness_fw_2 contents0 contents;

  let d00 = dist.(0sz);
  let d01 = dist.(1sz);
  let d10 = dist.(2sz);
  let d11 = dist.(3sz);
  assert (pure (d00 == 0));
  assert (pure (d01 == 3));
  assert (pure (d10 == FW.inf));
  assert (pure (d11 == 0));

  admit()
}
