module Test.NaiveStringMatch

module Seq = FStar.Seq
open CLRS.Ch32.NaiveStringMatch.Spec

let text : Seq.seq int = Seq.seq_of_list [1; 2; 3; 2; 3]
let pattern : Seq.seq int = Seq.seq_of_list [2; 3]

(* === Soundness: match at position 1 === *)
let test_match_sound_1 () : Lemma (matches_at_dec text pattern 1 == true) =
  assert_norm (matches_at_dec text pattern 1 == true)

(* === Soundness: match at position 3 === *)
let test_match_sound_2 () : Lemma (matches_at_dec text pattern 3 == true) =
  assert_norm (matches_at_dec text pattern 3 == true)

(* === Soundness: no match at position 0 === *)
let test_match_sound_3 () : Lemma (matches_at_dec text pattern 0 == false) =
  assert_norm (matches_at_dec text pattern 0 == false)

(* === Soundness: count matches === *)
let test_count_sound () : Lemma (count_matches_up_to text pattern 5 == 2) =
  assert_norm (count_matches_up_to text pattern 5 == 2)


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_match_complete_1 (y:bool) : Lemma
  (requires matches_at_dec text pattern 1 == y)
  (ensures y == true) =
  assert_norm (matches_at_dec text pattern 1 == true)

let test_match_complete_2 (y:bool) : Lemma
  (requires matches_at_dec text pattern 3 == y)
  (ensures y == true) =
  assert_norm (matches_at_dec text pattern 3 == true)

let test_match_complete_3 (y:bool) : Lemma
  (requires matches_at_dec text pattern 0 == y)
  (ensures y == false) =
  assert_norm (matches_at_dec text pattern 0 == false)

let test_count_complete (y:int) : Lemma
  (requires count_matches_up_to text pattern 5 == y)
  (ensures y == 2) =
  assert_norm (count_matches_up_to text pattern 5 == 2)
