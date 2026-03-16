module Test.InsertionSort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch02.InsertionSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SS = CLRS.Common.SortSpec
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let seq3_repr (s: Seq.seq int) : Lemma
  (requires Seq.length s == 3)
  (ensures Seq.equal s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2]))
= assert (forall (i:nat). i < Seq.length s ==> Seq.index s i == Seq.index (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2]) i);
  Seq.lemma_eq_intro s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2])

let std_sort3 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\
              SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (Seq.length (Seq.seq_of_list [3; 1; 2]) == 3);
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert (Seq.length s == 3);
  assert (SP.count 1 s == 1);
  assert (SP.count 2 s == 1);
  assert (SP.count 3 s == 1);
  let a = Seq.index s 0 in
  let b = Seq.index s 1 in
  let c = Seq.index s 2 in
  seq3_repr s;
  Seq.lemma_eq_elim s (Seq.seq_of_list [a; b; c]);
  assert (a <= b);
  assert (b <= c);
  assert (SP.count 1 (Seq.seq_of_list [a; b; c]) == 1);
  assert (SP.count 2 (Seq.seq_of_list [a; b; c]) == 1);
  assert (SP.count 3 (Seq.seq_of_list [a; b; c]) == 1);
  assert_norm (SP.count 1 (Seq.seq_of_list [a; b; c]) ==
               (if a = 1 then 1 else 0) +
               (if b = 1 then 1 else 0) +
               (if c = 1 then 1 else 0));
  assert_norm (SP.count 2 (Seq.seq_of_list [a; b; c]) ==
               (if a = 2 then 1 else 0) +
               (if b = 2 then 1 else 0) +
               (if c = 2 then 1 else 0));
  assert_norm (SP.count 3 (Seq.seq_of_list [a; b; c]) ==
               (if a = 3 then 1 else 0) +
               (if b = 3 then 1 else 0) +
               (if c = 3 then 1 else 0))

let input_is_sort3 (s0: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 3 /\
    Seq.index s0 0 == 3 /\
    Seq.index s0 1 == 1 /\
    Seq.index s0 2 == 2)
  (ensures Seq.equal s0 (Seq.seq_of_list [3; 1; 2]))
= assert_norm (Seq.length (Seq.seq_of_list [3; 1; 2]) == 3);
  assert (forall (i:nat). i < Seq.length s0 ==> Seq.index s0 i == Seq.index (Seq.seq_of_list [3; 1; 2]) i);
  Seq.lemma_eq_intro s0 (Seq.seq_of_list [3; 1; 2])

let completeness_sort3 (s0 s: Seq.seq int) : Lemma
  (requires
    Seq.length s0 == 3 /\
    Seq.index s0 0 == 3 /\
    Seq.index s0 1 == 1 /\
    Seq.index s0 2 == 2 /\
    Seq.length s == 3 /\
    SS.sorted s /\
    SS.permutation s0 s)
  (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= input_is_sort3 s0;
  Seq.lemma_eq_elim s0 (Seq.seq_of_list [3; 1; 2]);
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  std_sort3 s

#pop-options

fn test_insertion_sort ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);

  let ctr = GR.alloc #nat 0;
  insertion_sort arr 3sz ctr;

  with s. assert (A.pts_to arr s);
  completeness_sort3 s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 2));
  assert (pure (v2 == 3));

  admit()
}
