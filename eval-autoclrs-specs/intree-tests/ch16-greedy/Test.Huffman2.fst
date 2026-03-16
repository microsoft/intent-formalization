module Test.Huffman2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch16.Huffman.Impl
open CLRS.Ch16.Huffman.Defs

module A = Pulse.Lib.Array
module HOpt = CLRS.Ch16.Huffman.Optimality
module HSpec = CLRS.Ch16.Huffman.Spec
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_huffman_cost (ft: HSpec.htree) (freq_seq: Seq.seq int) : Lemma
  (requires Seq.length freq_seq == 2 /\
            Seq.index freq_seq 0 == 3 /\
            Seq.index freq_seq 1 == 4 /\
            HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list freq_seq 0))
  (ensures HSpec.cost ft == 7)
= assert (seq_to_pos_list freq_seq 2 == []);
  assert (seq_to_pos_list freq_seq 1 == [4]);
  assert (seq_to_pos_list freq_seq 0 == [3; 4]);
  assert (HSpec.cost ft == HOpt.greedy_cost [3; 4]);
  HOpt.greedy_cost_sorted_unfold [3; 4];
  HOpt.greedy_cost_singleton 7;
  assert (HOpt.greedy_cost [3; 4] == 7);
  assert (HSpec.cost ft == 7)
#pop-options

fn test_huffman ()
  requires emp
  returns _: unit
  ensures emp
{
  let fv = V.alloc 3 2sz;
  V.to_array_pts_to fv;
  let freqs = V.vec_to_array fv;
  rewrite (A.pts_to (V.vec_to_array fv) (Seq.create 2 3))
       as (A.pts_to freqs (Seq.create 2 3));
  freqs.(0sz) <- 3;
  freqs.(1sz) <- 4;

  let tree_ptr = huffman_tree freqs 2sz;

  with s_final.
    assert (A.pts_to freqs s_final);
  with ft.
    assert (is_htree tree_ptr ft **
            pure (HSpec.cost ft == HOpt.greedy_cost (seq_to_pos_list s_final 0) /\
                  HSpec.same_frequency_multiset ft (seq_to_pos_list s_final 0) /\
                  HSpec.is_wpl_optimal ft (seq_to_pos_list s_final 0)));
  completeness_huffman_cost ft s_final;
  assert (pure (HSpec.cost ft == 7));

  admit()
}
