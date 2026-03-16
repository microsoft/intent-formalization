module Test.FloydWarshall
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
module FWT = CLRS.Ch25.FloydWarshall.SpecTest

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"

let fw_test_input (contents0: Seq.seq int) : Lemma
  (requires
    Seq.length contents0 == 9 /\
    Seq.index contents0 0 == 0 /\
    Seq.index contents0 1 == 5 /\
    Seq.index contents0 2 == FW.inf /\
    Seq.index contents0 3 == 50 /\
    Seq.index contents0 4 == 0 /\
    Seq.index contents0 5 == 15 /\
    Seq.index contents0 6 == 30 /\
    Seq.index contents0 7 == FW.inf /\
    Seq.index contents0 8 == 0)
  (ensures Seq.equal contents0 FWT.test_adj)
= assert_norm (Seq.length FWT.test_adj == 9);
  assert (forall (i:nat). i < Seq.length contents0 ==> Seq.index contents0 i == Seq.index FWT.test_adj i);
  Seq.lemma_eq_intro contents0 FWT.test_adj

let completeness_fw_3 (contents0 contents: Seq.seq int) : Lemma
  (requires
    Seq.length contents0 == 9 /\
    Seq.index contents0 0 == 0 /\
    Seq.index contents0 1 == 5 /\
    Seq.index contents0 2 == FW.inf /\
    Seq.index contents0 3 == 50 /\
    Seq.index contents0 4 == 0 /\
    Seq.index contents0 5 == 15 /\
    Seq.index contents0 6 == 30 /\
    Seq.index contents0 7 == FW.inf /\
    Seq.index contents0 8 == 0 /\
    contents == FW.fw_outer contents0 3 0)
  (ensures
    Seq.index contents 0 == 0 /\
    Seq.index contents 1 == 5 /\
    Seq.index contents 2 == 20 /\
    Seq.index contents 3 == 45 /\
    Seq.index contents 4 == 0 /\
    Seq.index contents 5 == 15 /\
    Seq.index contents 6 == 30 /\
    Seq.index contents 7 == 35 /\
    Seq.index contents 8 == 0)
= fw_test_input contents0;
  Seq.lemma_eq_elim contents0 FWT.test_adj;
  assert (contents == FW.fw_outer FWT.test_adj 3 0);
  FWT.test_correctness 0 0; FWT.test_00 ();
  FWT.test_correctness 0 1; FWT.test_01 ();
  FWT.test_correctness 0 2; FWT.test_02 ();
  FWT.test_correctness 1 0; FWT.test_10 ();
  FWT.test_correctness 1 1; FWT.test_11 ();
  FWT.test_correctness 1 2; FWT.test_12 ();
  FWT.test_correctness 2 0; FWT.test_20 ();
  FWT.test_correctness 2 1; FWT.test_21 ();
  FWT.test_correctness 2 2; FWT.test_22 ();
  assert (Seq.index contents 0 == 0);
  assert (Seq.index contents 1 == 5);
  assert (Seq.index contents 2 == 20);
  assert (Seq.index contents 3 == 45);
  assert (Seq.index contents 4 == 0);
  assert (Seq.index contents 5 == 15);
  assert (Seq.index contents 6 == 30);
  assert (Seq.index contents 7 == 35);
  assert (Seq.index contents 8 == 0)

#pop-options

fn test_floyd_warshall ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 9sz;
  V.to_array_pts_to v;
  let dist = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 9 0)) as (A.pts_to dist (Seq.create 9 0));
  dist.(0sz) <- 0;
  dist.(1sz) <- 5;
  dist.(2sz) <- FW.inf;
  dist.(3sz) <- 50;
  dist.(4sz) <- 0;
  dist.(5sz) <- 15;
  dist.(6sz) <- 30;
  dist.(7sz) <- FW.inf;
  dist.(8sz) <- 0;

  with contents0. assert (A.pts_to dist contents0);

  let ctr = GR.alloc #nat 0;
  floyd_warshall dist 3sz ctr;

  with contents. assert (A.pts_to dist contents);
  completeness_fw_3 contents0 contents;

  let d00 = dist.(0sz);
  let d01 = dist.(1sz);
  let d02 = dist.(2sz);
  let d10 = dist.(3sz);
  let d11 = dist.(4sz);
  let d12 = dist.(5sz);
  let d20 = dist.(6sz);
  let d21 = dist.(7sz);
  let d22 = dist.(8sz);
  assert (pure (d00 == 0));
  assert (pure (d01 == 5));
  assert (pure (d02 == 20));
  assert (pure (d10 == 45));
  assert (pure (d11 == 0));
  assert (pure (d12 == 15));
  assert (pure (d20 == 30));
  assert (pure (d21 == 35));
  assert (pure (d22 == 0));

  admit()
}
