module Test.KMP

open FStar.Seq
open CLRS.Ch32.KMP.Spec

(* Test pattern: [1; 2; 1], text: [1; 2; 1; 2; 1] *)
let text : seq int = seq_of_list [1; 2; 1; 2; 1]
let pattern : seq int = seq_of_list [1; 2; 1]

(* === Soundness: matched_prefix_at — 3 characters match at position 3 === *)
(* text[0..2] = [1; 2; 1] matches pattern[0..2] = [1; 2; 1] *)
let test_match_sound () : Lemma (matched_prefix_at text pattern 3 3) = ()

(* === Soundness: matched_prefix_at — partial match of 1 character at position 1 === *)
let test_partial_match () : Lemma (matched_prefix_at text pattern 1 1) = ()

(* === Soundness: matched_prefix_at — 0 characters always match === *)
let test_zero_match () : Lemma (matched_prefix_at text pattern 0 0) = ()

(* === Completeness: no 3-character match at position 4 === *)
(* text[1..3] = [2; 1; 2] ≠ pattern = [1; 2; 1] *)
[@@expect_failure]
let test_match_complete () : Lemma (matched_prefix_at text pattern 4 3) = ()
