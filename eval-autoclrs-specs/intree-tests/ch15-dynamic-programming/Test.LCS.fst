module Test.LCS

open FStar.Seq
open CLRS.Ch15.LCS.Spec

(* === Soundness: LCS of [1;2;3] and [2;3;4] has length 2 === *)
let x1 : seq int = seq_of_list [1; 2; 3]
let y1 : seq int = seq_of_list [2; 3; 4]

let test_lcs_sound_1 () : Lemma (lcs_length x1 y1 3 3 == 2) =
  assert_norm (lcs_length x1 y1 3 3 == 2)

(* === Soundness: identical sequences have LCS = length === *)
let x2 : seq int = seq_of_list [1; 2; 3]
let y2 : seq int = seq_of_list [1; 2; 3]

let test_lcs_sound_2 () : Lemma (lcs_length x2 y2 3 3 == 3) =
  assert_norm (lcs_length x2 y2 3 3 == 3)

(* === Soundness: disjoint sequences have LCS = 0 === *)
let x3 : seq int = seq_of_list [1; 2]
let y3 : seq int = seq_of_list [3; 4]

let test_lcs_sound_3 () : Lemma (lcs_length x3 y3 2 2 == 0) =
  assert_norm (lcs_length x3 y3 2 2 == 0)

(* === Soundness: base case with empty === *)
let test_lcs_sound_4 () : Lemma (lcs_length x1 y1 0 3 == 0) = ()

(* === Completeness: wrong LCS length === *)
[@@expect_failure]
let test_lcs_complete_1 () : Lemma (lcs_length x1 y1 3 3 == 3) =
  assert_norm (lcs_length x1 y1 3 3 == 3)

[@@expect_failure]
let test_lcs_complete_2 () : Lemma (lcs_length x2 y2 3 3 == 2) =
  assert_norm (lcs_length x2 y2 3 3 == 2)
