module Test.BinarySearch3
#lang-pulse

(* Second completeness example — different input *)

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
let sorted_input_246810 (s0: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 5 /\
    Seq.index s0 0 == 2 /\
    Seq.index s0 1 == 4 /\
    Seq.index s0 2 == 6 /\
    Seq.index s0 3 == 8 /\
    Seq.index s0 4 == 10)
  (ensures BS.is_sorted s0)
= assert (BS.is_sorted s0)

let completeness_found (s0: Seq.seq int) (result: SZ.t) : Lemma
  (requires
    Seq.length s0 == 5 /\
    Seq.index s0 0 == 2 /\
    Seq.index s0 1 == 4 /\
    Seq.index s0 2 == 6 /\
    Seq.index s0 3 == 8 /\
    Seq.index s0 4 == 10 /\
    SZ.v result <= 5 /\
    (SZ.v result < 5 ==> (
      SZ.v result < Seq.length s0 /\
      Seq.index s0 (SZ.v result) == 8
    )) /\
    (SZ.v result == 5 ==> (
      forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i =!= 8
    )))
  (ensures result == 3sz)
= if result = 5sz then begin
    assert (Seq.index s0 3 =!= 8);
    assert False
  end else begin
    assert (Seq.index s0 (SZ.v result) == 8);
    assert (SZ.v result == 3);
    assert (result == 3sz)
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
  arr.(0sz) <- 2;
  arr.(1sz) <- 4;
  arr.(2sz) <- 6;
  arr.(3sz) <- 8;
  arr.(4sz) <- 10;

  with s0. assert (A.pts_to arr s0);
  sorted_input_246810 s0;

  let ctr = GR.alloc #nat 0;
  let result = binary_search arr 5sz 8 ctr;

  completeness_found s0 result;
  assert (pure (result == 3sz));

  admit()
}
