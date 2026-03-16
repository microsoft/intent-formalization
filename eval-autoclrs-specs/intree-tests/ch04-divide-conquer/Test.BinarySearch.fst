module Test.BinarySearch
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
let sorted_input_12345 (s0: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 5 /\
    Seq.index s0 0 == 1 /\
    Seq.index s0 1 == 2 /\
    Seq.index s0 2 == 3 /\
    Seq.index s0 3 == 4 /\
    Seq.index s0 4 == 5)
  (ensures BS.is_sorted s0)
= assert (BS.is_sorted s0)

let completeness_found (s0: Seq.seq int) (result: SZ.t) : Lemma
  (requires
    Seq.length s0 == 5 /\
    Seq.index s0 0 == 1 /\
    Seq.index s0 1 == 2 /\
    Seq.index s0 2 == 3 /\
    Seq.index s0 3 == 4 /\
    Seq.index s0 4 == 5 /\
    SZ.v result <= 5 /\
    (SZ.v result < 5 ==> (
      SZ.v result < Seq.length s0 /\
      Seq.index s0 (SZ.v result) == 3
    )) /\
    (SZ.v result == 5 ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= 3
    )))
  (ensures result == 2sz)
= if result = 5sz then begin
    assert (Seq.index s0 2 =!= 3);
    assert False
  end else begin
    assert (Seq.index s0 (SZ.v result) == 3);
    assert (SZ.v result == 2);
    assert (result == 2sz)
  end
#pop-options

fn test_binary_search ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 5sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 5 0)) as (A.pts_to arr (Seq.create 5 0));
  arr.(0sz) <- 1;
  arr.(1sz) <- 2;
  arr.(2sz) <- 3;
  arr.(3sz) <- 4;
  arr.(4sz) <- 5;

  with s0. assert (A.pts_to arr s0);
  sorted_input_12345 s0;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 5sz 3 ctr;

  completeness_found s0 result;
  assert (pure (result == 2sz));

  admit()
}
