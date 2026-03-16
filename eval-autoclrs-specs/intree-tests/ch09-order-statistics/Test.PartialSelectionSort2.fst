module Test.PartialSelectionSort2
#lang-pulse

(* Second completeness example — different input *)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.BoundedIntegers
open FStar.SizeT
open FStar.Classical
open CLRS.Ch09.PartialSelectionSort.Impl
open CLRS.Ch09.PartialSelectionSort.Lemmas

module A = Pulse.Lib.Array
module V = Pulse.Lib.Vec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module GR = Pulse.Lib.GhostReference
module PSSSpec = CLRS.Ch09.PartialSelectionSort.Spec
module PSSLemmas = CLRS.Ch09.PartialSelectionSort.Lemmas

#push-options "--z3rlimit 200 --fuel 4 --ifuel 2"

let rec count_occ_eq_seq_count (s: Seq.seq int) (x: int)
  : Lemma (ensures PSSSpec.count_occ s x == Seq.count x s)
          (decreases Seq.length s)
  = if Seq.length s = 0 then ()
    else count_occ_eq_seq_count (Seq.tail s) x

let impl_perm_implies_spec_perm (s1 s2: Seq.seq int)
  : Lemma (requires permutation s1 s2)
          (ensures PSSSpec.is_permutation s1 s2)
  = reveal_opaque (`%permutation) (permutation s1 s2);
    FStar.Seq.Properties.perm_len s1 s2;
    let aux (x: int) : Lemma (PSSSpec.count_occ s1 x == PSSSpec.count_occ s2 x) =
      count_occ_eq_seq_count s1 x;
      count_occ_eq_seq_count s2 x
    in
    Classical.forall_intro aux

let select_pre () : Lemma (ensures SZ.v 3sz > 0 /\ SZ.v 1sz > 0 /\ SZ.v 1sz <= SZ.v 3sz) =
  assert_norm (SZ.v 3sz > 0 /\ SZ.v 1sz > 0 /\ SZ.v 1sz <= SZ.v 3sz)

let select_spec_0 () : Lemma (PSSSpec.select_spec (Seq.seq_of_list [7; 1; 4]) 0 == 1) =
  assert_norm (PSSSpec.select_spec (Seq.seq_of_list [7; 1; 4]) 0 == 1)

```pulse
fn test_select ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc 0 3sz;
  V.to_array_pts_to v;
  let arr = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 3 0)) as (A.pts_to arr (Seq.create 3 0));
  A.pts_to_len arr;
  assert (pure (A.length arr == SZ.v 3sz));
  arr.(0sz) <- 7;
  arr.(1sz) <- 1;
  arr.(2sz) <- 4;

  with s0. assert (A.pts_to arr s0);
  A.pts_to_len arr;
  assert (pure (Seq.length s0 == SZ.v 3sz));
  assert (pure (A.length arr == SZ.v 3sz));
  select_pre ();

  let ctr = GR.alloc #nat 0;
  let result = select arr #s0 3sz 1sz ctr #(hide 0);
  // k=1: select_spec [7;1;4] 0 = 1 (0-indexed in spec, 1-indexed k)
  // result == Seq.index s_final (k-1) = s_final[0] = smallest = 1
  with s_final. assert (A.pts_to arr s_final);
  impl_perm_implies_spec_perm s0 s_final;
  assert (pure (forall (i: nat). 0 < i /\ i < Seq.length s_final ==> Seq.index s_final 0 <= Seq.index s_final i));
  PSSLemmas.pulse_correctness_hint s0 s_final 0;
  select_spec_0 ();
  assert (pure (result == 1));

  with cf. assert (GR.pts_to ctr cf);
  GR.free ctr;
  with s2. assert (A.pts_to arr s2);
  rewrite (A.pts_to arr s2) as (A.pts_to (V.vec_to_array v) s2);
  V.to_vec_pts_to v;
  V.free v;
}
```

#pop-options
