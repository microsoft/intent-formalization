module Test.Quickselect

module Seq = FStar.Seq
open CLRS.Ch09.Quickselect.Spec

(* partition_ordered: elements left of pivot <= pivot, right >= pivot *)

(* === Soundness: correctly partitioned array [1; 2; 3; 5; 8; 7; 9] with pivot at index 3 === *)
let partitioned : Seq.seq int = Seq.seq_of_list [1; 2; 3; 5; 8; 7; 9]

let test_partition_sound () : Lemma (partition_ordered partitioned 0 3 7) = ()

(* === Soundness: unchanged_outside === *)
let s1 : Seq.seq int = Seq.seq_of_list [1; 2; 3; 4; 5]
let s2 : Seq.seq int = Seq.seq_of_list [1; 3; 2; 4; 5]

let test_unchanged_sound () : Lemma (unchanged_outside s1 s2 1 3) = ()

(* === Soundness: permutation reflexive === *)
let test_perm_refl () : Lemma (permutation s1 s1) =
  permutation_refl s1

(* Completeness note: partition_ordered, unchanged_outside, permutation are
   relational property checks (prop predicates) — no single output variable
   to quantify over. These test individual spec components; full algorithm
   completeness requires combining all predicates. *)
