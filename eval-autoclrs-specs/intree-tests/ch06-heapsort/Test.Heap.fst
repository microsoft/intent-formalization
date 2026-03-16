module Test.Heap
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch06.Heap.Impl
open CLRS.Ch06.Heap.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module V = Pulse.Lib.Vec

(* ================================================================
   Completeness test for heapsort (Pulse implementation)

   Input: [3; 1; 2]
   Expected output: [1; 2; 3]
   Impl function: heapsort (CLRS.Ch06.Heap.Impl)
   ================================================================ *)

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let seq3_repr (s: Seq.seq int) : Lemma
  (requires Seq.length s == 3)
  (ensures Seq.equal s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2]))
= assert (forall (i:nat). i < Seq.length s ==> Seq.index s i == Seq.index (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2]) i);
  Seq.lemma_eq_intro s (Seq.seq_of_list [Seq.index s 0; Seq.index s 1; Seq.index s 2])

let std_sort3 (s: Seq.seq int)
  : Lemma
    (requires sorted s /\
              SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
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

let completeness_heapsort (s: Seq.seq int) (s0: Seq.seq int) : Lemma
  (requires
    s0 `Seq.equal` Seq.seq_of_list [3; 1; 2] /\
    Seq.length s == 3 /\
    sorted s /\
    permutation s0 s)
  (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= Seq.lemma_eq_elim s0 (Seq.seq_of_list [3; 1; 2]);
  reveal_opaque (`%permutation) (permutation s0 s);
  std_sort3 s
#pop-options

```pulse
(* Completeness: y = heapsort(x); assert(y == expected) *)
fn test_heapsort ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: [3; 1; 2]
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0))
       as (A.pts_to arr (Seq.create 3 0));
  arr.(0sz) <- 3;
  arr.(1sz) <- 1;
  arr.(2sz) <- 2;

  with s0. assert (A.pts_to arr s0);

  // Ghost complexity counter
  let ctr = GR.alloc #nat 0;

  // y = heapsort(x)
  heapsort arr 3sz ctr;

  // Extract postcondition
  with s. assert (A.pts_to arr s);
  with cf. assert (GR.pts_to ctr cf);

  // Apply completeness lemma
  completeness_heapsort s s0;

  // Read and verify
  let v0 = arr.(0sz);
  let v1 = arr.(1sz);
  let v2 = arr.(2sz);
  assert (pure (v0 == 1));   // ✅ output[0]
  assert (pure (v1 == 2));   // ✅ output[1]
  assert (pure (v2 == 3));   // ✅ output[2]

  admit()  // skip cleanup
}
```
