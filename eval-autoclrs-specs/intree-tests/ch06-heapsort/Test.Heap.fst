module Test.Heap

module Seq = FStar.Seq
open CLRS.Ch06.Heap.Spec

(* === Soundness: heap index functions === *)
let test_parent () : Lemma (parent_idx 1 == 0 /\ parent_idx 2 == 0 /\
                            parent_idx 3 == 1 /\ parent_idx 4 == 1) = ()

let test_left () : Lemma (left_idx 0 == 1 /\ left_idx 1 == 3 /\ left_idx 2 == 5) = ()

let test_right () : Lemma (right_idx 0 == 2 /\ right_idx 1 == 4 /\ right_idx 2 == 6) = ()

(* === Soundness: max-heap property on [10; 8; 6; 4; 2] === *)
let heap_seq : Seq.seq int = Seq.seq_of_list [10; 8; 6; 4; 2]

let test_heap_down_root () : Lemma (heap_down_at heap_seq 5 0) = ()
let test_heap_down_1 () : Lemma (heap_down_at heap_seq 5 1) = ()
let test_heap_down_2 () : Lemma (heap_down_at heap_seq 5 2) = ()

(* === Soundness: NOT a max-heap [4; 10; 3; 2; 1] (root < left child) === *)
let bad_heap : Seq.seq int = Seq.seq_of_list [4; 10; 3; 2; 1]

[@@expect_failure]
let test_heap_down_bad () : Lemma (heap_down_at bad_heap 5 0) = ()

(* === Soundness: swap changes indices === *)
let test_swap_sound () : Lemma (
  Seq.index (swap_seq heap_seq 0 4) 0 == 2 /\
  Seq.index (swap_seq heap_seq 0 4) 4 == 10
) = ()

(* === Completeness: wrong swap === *)
[@@expect_failure]
let test_swap_complete () : Lemma (
  Seq.index (swap_seq heap_seq 0 4) 0 == 10
) = ()
