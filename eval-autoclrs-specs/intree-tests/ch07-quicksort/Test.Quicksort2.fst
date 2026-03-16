(* Second completeness example — input [5;1;3] → [1;3;5] *)
module Test.Quicksort2
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch07.Quicksort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SS = CLRS.Common.SortSpec
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let seq3_repr2 (s: Seq.seq int) : Lemma
  (requires Seq.length s == 3)
  (ensures Seq.equal s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2]))
= Seq.lemma_eq_intro s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2])

let std_sort3_v2 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\
              SP.permutation int (Seq.seq_of_list [5; 1; 3]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 3 /\ Seq.index s 2 == 5)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  SP.perm_len (Seq.seq_of_list [5; 1; 3]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count 5 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count 2 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count 6 (Seq.seq_of_list [5; 1; 3]) == 0);
  let a = Seq.index s 0 in let b = Seq.index s 1 in let c = Seq.index s 2 in
  seq3_repr2 s;
  Seq.lemma_eq_elim s (Seq.seq_of_list [a; b; c]);
  assert_norm (SP.count 1 (Seq.seq_of_list [a; b; c]) ==
               (if a = 1 then 1 else 0) + (if b = 1 then 1 else 0) + (if c = 1 then 1 else 0));
  assert_norm (SP.count 3 (Seq.seq_of_list [a; b; c]) ==
               (if a = 3 then 1 else 0) + (if b = 3 then 1 else 0) + (if c = 3 then 1 else 0));
  assert_norm (SP.count 5 (Seq.seq_of_list [a; b; c]) ==
               (if a = 5 then 1 else 0) + (if b = 5 then 1 else 0) + (if c = 5 then 1 else 0))

let completeness_quicksort2 (s0 s: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 3 /\
    Seq.index s0 0 == 5 /\ Seq.index s0 1 == 1 /\ Seq.index s0 2 == 3 /\
    Seq.length s == 3 /\ SS.sorted s /\ SS.permutation s0 s)
  (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 3 /\ Seq.index s 2 == 5)
= Seq.lemma_eq_intro s0 (Seq.seq_of_list [5; 1; 3]);
  Seq.lemma_eq_elim s0 (Seq.seq_of_list [5; 1; 3]);
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  std_sort3_v2 s

#pop-options

fn test_quicksort2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 1;
  arr.(2sz) <- 3;

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  quicksort arr 3sz ctr;

  with s. assert (A.pts_to arr s);
  completeness_quicksort2 s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 3));
  assert (pure (v2 == 5));

  admit()
}
