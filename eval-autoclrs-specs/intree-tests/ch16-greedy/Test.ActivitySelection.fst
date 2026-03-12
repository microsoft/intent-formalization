module Test.ActivitySelection

open FStar.List.Tot
module Seq = FStar.Seq
open CLRS.Ch16.ActivitySelection.Spec

(* Activities: start=[1;3;4;6], finish=[3;5;6;9]
   Activity 0: [1,3), Activity 1: [3,5), Activity 2: [4,6), Activity 3: [6,9)
   Compatible: {0,1,3} (0 ends at 3 = start of 1; 1 ends at 5 < 6 = start of 3)
*)
let start : Seq.seq int = Seq.seq_of_list [1; 3; 4; 6]
let finish : Seq.seq int = Seq.seq_of_list [3; 5; 6; 9]

(* === Soundness: activities are finish-sorted === *)
let test_sorted_sound () : Lemma (finish_sorted finish) = ()

(* === Soundness: activities 0 and 1 are compatible === *)
let test_compat_sound () : Lemma (compatible start finish 0 1) = ()

(* === Soundness: activities 1 and 2 are NOT compatible (overlap) === *)
[@@expect_failure]
let test_incompat () : Lemma (compatible start finish 1 2) = ()

(* === Soundness: {0, 1, 3} is mutually compatible === *)
let test_mutual_compat_sound () : Lemma (mutually_compatible start finish [0; 1; 3]) = ()

(* === Completeness: {0, 1, 2} is NOT mutually compatible (1 and 2 overlap) === *)
[@@expect_failure]
let test_mutual_compat_complete () : Lemma (mutually_compatible start finish [0; 1; 2]) = ()
