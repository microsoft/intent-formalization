(* Second completeness example — input [5;1;3] → [1;3;5] *)
module Test.CountingSort2
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open CLRS.Ch08.CountingSort.Impl

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module S = CLRS.Ch08.CountingSort.Spec
module GR = Pulse.Lib.GhostReference

#push-options "--z3rlimit 400 --fuel 8 --ifuel 4"

let std_sort3_nat_v2 (s: Seq.seq nat)
  : Lemma
    (requires Seq.length s == 3 /\
              (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j 3 ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation nat (Seq.seq_of_list [5; 1; 3]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 3 /\ Seq.index s 2 == 5)
= SP.perm_len (Seq.seq_of_list [5; 1; 3]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count 5 (Seq.seq_of_list [5; 1; 3]) == 1);
  assert_norm (SP.count #nat 0 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count #nat 2 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count #nat 4 (Seq.seq_of_list [5; 1; 3]) == 0);
  assert_norm (SP.count #nat 6 (Seq.seq_of_list [5; 1; 3]) == 0)

let completeness_csort3_v2 (s0 s: Seq.seq nat)
  : Lemma
    (requires Seq.length s0 == 3 /\
              Seq.index s0 0 == 5 /\
              Seq.index s0 1 == 1 /\
              Seq.index s0 2 == 3 /\
              Seq.length s == 3 /\
              S.sorted s /\
              S.permutation s0 s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 3 /\ Seq.index s 2 == 5)
= Seq.lemma_eq_intro s0 (Seq.seq_of_list [5; 1; 3]);
  Seq.lemma_eq_elim s0 (Seq.seq_of_list [5; 1; 3]);
  reveal_opaque (`%S.permutation) (S.permutation s0 s);
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:nat). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3_nat_v2 s

```pulse
fn test_counting_sort2 ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc #nat 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create #nat 3 0));
  arr.(0sz) <- 5;
  arr.(1sz) <- 1;
  arr.(2sz) <- 3;

  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;
  assert (pure (A.length arr == SZ.v 3sz));
  assert (pure (Seq.length s0 == 3));

  counting_sort_inplace arr 3sz 6sz;

  with s. assert (A.pts_to arr s);
  A.pts_to_len arr;
  assert (pure (Seq.length s == 3));
  completeness_csort3_v2 s0 s;

  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));
  assert (pure (v1 == 3));
  assert (pure (v2 == 5));

  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
