module Test.MatrixMultiply
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch04.MatrixMultiply.Impl
open CLRS.Ch04.MatrixMultiply.Spec

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq

let mm_indices ()
  : Lemma (flat_index 2 0 0 == 0 /\
           flat_index 2 0 1 == 1 /\
           flat_index 2 1 0 == 2 /\
           flat_index 2 1 1 == 3)
  = assert_norm (flat_index 2 0 0 == 0 /\
                 flat_index 2 0 1 == 1 /\
                 flat_index 2 1 0 == 2 /\
                 flat_index 2 1 1 == 3)

let mm00 ()
  : Lemma (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 0 0 2 == 19)
  = assert_norm (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 0 0 2 == 19)

let mm01 ()
  : Lemma (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 0 1 2 == 22)
  = assert_norm (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 0 1 2 == 22)

let mm10 ()
  : Lemma (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 1 0 2 == 43)
  = assert_norm (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 1 0 2 == 43)

let mm11 ()
  : Lemma (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 1 1 2 == 50)
  = assert_norm (dot_product_spec (Seq.seq_of_list [1; 2; 3; 4]) (Seq.seq_of_list [5; 6; 7; 8]) 2 1 1 2 == 50)

let mm_2sz_pre ()
  : Lemma
    (ensures SZ.v 2sz > 0 /\
             SZ.v 4sz == op_Multiply (SZ.v 2sz) (SZ.v 2sz) /\
             SZ.fits (op_Multiply (SZ.v 2sz) (SZ.v 2sz)))
  = assert_norm (SZ.v 2sz > 0 /\
                 SZ.v 4sz == op_Multiply (SZ.v 2sz) (SZ.v 2sz) /\
                 SZ.fits (op_Multiply (SZ.v 2sz) (SZ.v 2sz)))

```pulse
fn test_matrix_multiply_2x2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let av = V.alloc 0 4sz;
  V.to_array_pts_to av;
  let a_arr = V.vec_to_array av;
  rewrite (A.pts_to (V.vec_to_array av) (Seq.create 4 0)) as (A.pts_to a_arr (Seq.create 4 0));
  A.pts_to_len a_arr;
  assert (pure (A.length a_arr == SZ.v 4sz));
  a_arr.(0sz) <- 1;
  a_arr.(1sz) <- 2;
  a_arr.(2sz) <- 3;
  a_arr.(3sz) <- 4;

  let bv = V.alloc 0 4sz;
  V.to_array_pts_to bv;
  let b_arr = V.vec_to_array bv;
  rewrite (A.pts_to (V.vec_to_array bv) (Seq.create 4 0)) as (A.pts_to b_arr (Seq.create 4 0));
  A.pts_to_len b_arr;
  assert (pure (A.length b_arr == SZ.v 4sz));
  b_arr.(0sz) <- 5;
  b_arr.(1sz) <- 6;
  b_arr.(2sz) <- 7;
  b_arr.(3sz) <- 8;

  let cv = V.alloc 0 4sz;
  V.to_array_pts_to cv;
  let c_arr = V.vec_to_array cv;
  rewrite (A.pts_to (V.vec_to_array cv) (Seq.create 4 0)) as (A.pts_to c_arr (Seq.create 4 0));
  A.pts_to_len c_arr;
  assert (pure (A.length c_arr == SZ.v 4sz));

  with sa0. assert (A.pts_to a_arr sa0);
  with sb0. assert (A.pts_to b_arr sb0);
  with sc0. assert (A.pts_to c_arr sc0);
  A.pts_to_len a_arr;
  A.pts_to_len b_arr;
  A.pts_to_len c_arr;
  assert (pure (A.length a_arr == SZ.v 4sz));
  assert (pure (A.length b_arr == SZ.v 4sz));
  assert (pure (A.length c_arr == SZ.v 4sz));
  mm_2sz_pre ();
  assert (pure (Seq.length sa0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));
  assert (pure (Seq.length sb0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));
  assert (pure (Seq.length sc0 == op_Multiply (SZ.v 2sz) (SZ.v 2sz)));

  let ctr = GR.alloc #nat 0;
  matrix_multiply a_arr b_arr c_arr 2sz ctr;

  with sc1. assert (A.pts_to c_arr sc1);
  mm_indices ();
  mm00 ();
  mm01 ();
  mm10 ();
  mm11 ();
  assert (pure (Seq.index sc1 0 == 19));
  assert (pure (Seq.index sc1 1 == 22));
  assert (pure (Seq.index sc1 2 == 43));
  assert (pure (Seq.index sc1 3 == 50));

  let c00 = c_arr.(0sz);
  let c01 = c_arr.(1sz);
  let c10 = c_arr.(2sz);
  let c11 = c_arr.(3sz);
  assert (pure (c00 == 19));
  assert (pure (c01 == 22));
  assert (pure (c10 == 43));
  assert (pure (c11 == 50));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;

  with sc2. assert (A.pts_to c_arr sc2);
  rewrite (A.pts_to c_arr sc2) as (A.pts_to (V.vec_to_array cv) sc2);
  V.to_vec_pts_to cv;
  V.free cv;

  with sb1. assert (A.pts_to b_arr sb1);
  rewrite (A.pts_to b_arr sb1) as (A.pts_to (V.vec_to_array bv) sb1);
  V.to_vec_pts_to bv;
  V.free bv;

  with sa1. assert (A.pts_to a_arr sa1);
  rewrite (A.pts_to a_arr sa1) as (A.pts_to (V.vec_to_array av) sa1);
  V.to_vec_pts_to av;
  V.free av;
}
```
