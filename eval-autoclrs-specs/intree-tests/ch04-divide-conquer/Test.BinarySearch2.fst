(* Non-determinism test: this completeness check is expected to be unprovable *)
module Test.BinarySearch2
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch04.BinarySearch.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module BS = CLRS.Ch04.BinarySearch.Spec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let sorted_input_1335 (s0: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 4 /\
    Seq.index s0 0 == 1 /\
    Seq.index s0 1 == 3 /\
    Seq.index s0 2 == 3 /\
    Seq.index s0 3 == 5)
  (ensures BS.is_sorted s0)
= assert (BS.is_sorted s0)

let completeness_found_nondet (s0: Seq.seq int) (result: SZ.t) : Lemma
  (requires
    Seq.length s0 == 4 /\
    Seq.index s0 0 == 1 /\
    Seq.index s0 1 == 3 /\
    Seq.index s0 2 == 3 /\
    Seq.index s0 3 == 5 /\
    SZ.v result <= 4 /\
    (SZ.v result < 4 ==> (
      SZ.v result < Seq.length s0 /\
      Seq.index s0 (SZ.v result) == 3
    )) /\
    (SZ.v result == 4 ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= 3
    )))
  (ensures result == 1sz)
= admit()
#pop-options

fn test_binary_search2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 4sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 4 0)) as (A.pts_to arr (Seq.create 4 0));
  arr.(0sz) <- 1;
  arr.(1sz) <- 3;
  arr.(2sz) <- 3;
  arr.(3sz) <- 5;

  with s0. assert (A.pts_to arr s0);
  sorted_input_1335 s0;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 4sz 3 ctr;

  completeness_found_nondet s0 result;
  assert (pure (result == 1sz));

  admit()
}
