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
(* === Soundness: swap changes indices === *)
let test_swap_sound () : Lemma (
  Seq.index (swap_seq heap_seq 0 4) 0 == 2 /\
  Seq.index (swap_seq heap_seq 0 4) 4 == 10
) = ()

(* === Completeness (Appendix B): functional specs uniquely determine output === *)
let test_parent_complete (y:int) : Lemma
  (requires parent_idx 1 == y)
  (ensures y == 0) = ()

let test_left_complete (y:int) : Lemma
  (requires left_idx 0 == y)
  (ensures y == 1) = ()

let test_right_complete (y:int) : Lemma
  (requires right_idx 0 == y)
  (ensures y == 2) = ()

let test_swap_complete (y:int) : Lemma
  (requires Seq.index (swap_seq heap_seq 0 4) 0 == y)
  (ensures y == 2) = ()
