module Test.MatrixChain2
#lang-pulse

(* Second completeness example — different input *)

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
  : Lemma (mc_result (Seq.seq_of_list [5; 10; 20; 15]) 3 == 2500)
  = assert_norm (mc_result (Seq.seq_of_list [5; 10; 20; 15]) 3 == 2500)

```pulse
fn test_matrix_chain_basic ()
  requires emp
  returns _: unit
  ensures emp
{
  let dv = V.alloc 5 4sz;
  V.to_array_pts_to dv;
  let dims = V.vec_to_array dv;
  rewrite (A.pts_to (V.vec_to_array dv) (Seq.create 4 5)) as (A.pts_to dims (Seq.create 4 5));
  dims.(0sz) <- 5;
  dims.(1sz) <- 10;
  dims.(2sz) <- 20;
  dims.(3sz) <- 15;

  with s_dims. assert (A.pts_to dims s_dims);

  let nSz = 3sz;
  let result = matrix_chain_order dims nSz;

  mc_test ();
  assert (pure (result == 2500));

  with s1. assert (A.pts_to dims s1);
  rewrite (A.pts_to dims s1) as (A.pts_to (V.vec_to_array dv) s1);
  V.to_vec_pts_to dv;
  V.free dv;
}
```
