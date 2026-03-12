module Test.InsertionSort

module Seq = FStar.Seq
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec

let x : Seq.seq int = Seq.seq_of_list [3; 1; 2]
let y : Seq.seq int = Seq.seq_of_list [1; 2; 3]

(* === Soundness: sorted output that is a permutation of input === *)
let test_sound_1 () : Lemma (sorted y /\ permutation x y) =
  reveal_opaque (`%permutation) (permutation x y)

let x2 : Seq.seq int = Seq.seq_of_list [5; 3; 1; 4; 2]
let y2 : Seq.seq int = Seq.seq_of_list [1; 2; 3; 4; 5]

#push-options "--z3rlimit 50"
let test_sound_2 () : Lemma (sorted y2 /\ permutation x2 y2) =
  assert (Seq.index y2 0 <= Seq.index y2 1);
  assert (Seq.index y2 1 <= Seq.index y2 2);
  assert (Seq.index y2 2 <= Seq.index y2 3);
  assert (Seq.index y2 3 <= Seq.index y2 4);
  reveal_opaque (`%permutation) (permutation x2 y2)
#pop-options

(* === Completeness: wrong output (not sorted) === *)
let bad : Seq.seq int = Seq.seq_of_list [2; 1; 3]

[@@expect_failure]
let test_complete_1 () : Lemma (sorted bad /\ permutation x bad) =
  reveal_opaque (`%permutation) (permutation x bad)

(* === Completeness: wrong output (not a permutation) === *)
let bad2 : Seq.seq int = Seq.seq_of_list [1; 2; 4]

[@@expect_failure]
let test_complete_2 () : Lemma (sorted bad2 /\ permutation x bad2) =
  reveal_opaque (`%permutation) (permutation x bad2)
