module Test.Quicksort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch07.Quicksort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq

(* Completeness: y = quicksort(x); assert(y == expected) *)
fn test_quicksort_3 ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  // y = quicksort(x)
  quicksort arr 3sz;

  // assert(y == expected)
  with s. assert (A.pts_to arr s);
  assert (pure (s `Seq.equal` Seq.seq_of_list [1; 2; 3]));

  // cleanup
  rewrite (A.pts_to arr s) as (A.pts_to (V.vec_to_array v) s);
  V.to_vec_pts_to v;
  V.free v;
  ()
}
