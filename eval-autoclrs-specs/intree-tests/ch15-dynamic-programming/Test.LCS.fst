module Test.LCS
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch15.LCS.Impl
open CLRS.Ch15.LCS.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

let lcs_test ()
  : Lemma (lcs_length (Seq.seq_of_list [1; 2; 3]) (Seq.seq_of_list [2; 3; 4]) 3 3 == 2)
  = assert_norm (lcs_length (Seq.seq_of_list [1; 2; 3]) (Seq.seq_of_list [2; 3; 4]) 3 3 == 2)

let lcs_3sz_pre ()
  : Lemma
    (ensures SZ.v 3sz > 0 /\
             SZ.fits (op_Multiply (SZ.v 3sz + 1) (SZ.v 3sz + 1)))
  = assert_norm (SZ.v 3sz > 0 /\
                 SZ.fits (op_Multiply (SZ.v 3sz + 1) (SZ.v 3sz + 1)))

```pulse
fn test_lcs_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let xv = V.alloc 0 3sz;
  V.to_array_pts_to xv;
  let x_arr = V.vec_to_array xv;
  rewrite (A.pts_to (V.vec_to_array xv) (Seq.create 3 0)) as (A.pts_to x_arr (Seq.create 3 0));
  A.pts_to_len x_arr;
  assert (pure (A.length x_arr == SZ.v 3sz));
  x_arr.(0sz) <- 1;
  x_arr.(1sz) <- 2;
  x_arr.(2sz) <- 3;

  let yv = V.alloc 0 3sz;
  V.to_array_pts_to yv;
  let y_arr = V.vec_to_array yv;
  rewrite (A.pts_to (V.vec_to_array yv) (Seq.create 3 0)) as (A.pts_to y_arr (Seq.create 3 0));
  A.pts_to_len y_arr;
  assert (pure (A.length y_arr == SZ.v 3sz));
  y_arr.(0sz) <- 2;
  y_arr.(1sz) <- 3;
  y_arr.(2sz) <- 4;

  lcs_3sz_pre ();

  let ctr = GR.alloc #nat 0;
  let result = lcs x_arr y_arr 3sz 3sz ctr;

  lcs_test ();
  assert (pure (result == 2));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with sy1. assert (A.pts_to y_arr sy1);
  rewrite (A.pts_to y_arr sy1) as (A.pts_to (V.vec_to_array yv) sy1);
  V.to_vec_pts_to yv;
  V.free yv;

  with sx1. assert (A.pts_to x_arr sx1);
  rewrite (A.pts_to x_arr sx1) as (A.pts_to (V.vec_to_array xv) sx1);
  V.to_vec_pts_to xv;
  V.free xv;
}
```
