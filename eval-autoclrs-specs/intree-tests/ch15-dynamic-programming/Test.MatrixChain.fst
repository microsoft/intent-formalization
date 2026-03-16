module Test.MatrixChain
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch15.MatrixChain.Impl
open CLRS.Ch15.MatrixChain.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

let mc_test ()
  : Lemma (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)
  = assert_norm (mc_result (Seq.seq_of_list [10; 30; 5; 60]) 3 == 4500)

```pulse
fn test_matrix_chain_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let dv = V.alloc 10 4sz;
  V.to_array_pts_to dv;
  let dims = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 4 10)) as (A.pts_to dims (Seq.create 4 10));
  dims.(0sz) <- 10;
  dims.(1sz) <- 30;
  dims.(2sz) <- 5;
  dims.(3sz) <- 60;

  with s_dims. assert (A.pts_to dims s_dims);

  let result = matrix_chain_order dims 3sz;

  mc_test ();
  assert (pure (result == 4500));

  with s1. assert (A.pts_to dims s1);
  rewrite (A.pts_to dims s1) as (A.pts_to (V.vec_to_array dv) s1);
  V.to_vec_pts_to dv;
  V.free dv;
}
```
