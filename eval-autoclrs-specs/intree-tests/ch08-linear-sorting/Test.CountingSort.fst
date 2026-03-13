module Test.CountingSort

open FStar.Seq
module Seq = FStar.Seq
open CLRS.Ch08.CountingSort.Spec

(* === Soundness: sorted predicate on sorted sequence of nats === *)
let sorted_seq : Seq.seq nat = Seq.seq_of_list [1; 2; 3; 4; 5]

let test_sorted_sound () : Lemma (sorted sorted_seq) = ()

(* === Soundness: in_range predicate === *)
let test_in_range_sound () : Lemma (in_range sorted_seq 5) = ()

(* === Soundness: sorted_prefix === *)
let test_sorted_prefix () : Lemma (sorted_prefix sorted_seq 3) = ()

(* === Soundness: permutation is reflexive === *)
let test_perm_refl () : Lemma (permutation sorted_seq sorted_seq) =
  reveal_opaque (`%permutation) (permutation sorted_seq sorted_seq)

(* Completeness note: sorted, in_range, sorted_prefix, permutation are property
   checks (prop predicates on fixed inputs) — no output variable to quantify over.
   Algorithm-level sorting completeness is demonstrated in Test.InsertionSort. *)
