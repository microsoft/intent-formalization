module Test.GrahamScan

open FStar.Mul
module Seq = FStar.Seq
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.GrahamScan.Spec

(* Points: (0,0), (2,0), (1,2), (1,1)
   xs = [0; 2; 1; 1], ys = [0; 0; 2; 1] *)
let xs : Seq.seq int = Seq.seq_of_list [0; 2; 1; 1]
let ys : Seq.seq int = Seq.seq_of_list [0; 0; 2; 1]

(* === Soundness: find_bottom_spec returns bottommost point === *)
(* Point 0 (0,0) and point 1 (2,0) both have y=0; 0 has smaller x → index 0 *)
let test_bottom () : Lemma (find_bottom_spec xs ys == 0) =
  assert_norm (find_bottom_spec xs ys == 0)

(* === Soundness: cross_prod (re-exported) === *)
let test_cross () : Lemma (cross_prod 0 0 1 0 0 1 == 1) = ()

(* === Soundness: polar_cmp_spec === *)
(* From pivot (0,0), compare points (2,0) and (1,2):
   cross product = (2-0)*(2-0) - (1-0)*(0-0) = 4 - 0 = 4 > 0
   So point 1 (2,0) has smaller polar angle *)
let test_polar () : Lemma (polar_cmp_spec xs ys 0 1 2 > 0) =
  assert_norm (polar_cmp_spec xs ys 0 1 2 > 0)

(* === Completeness: wrong bottom point === *)
[@@expect_failure]
let test_bottom_complete () : Lemma (find_bottom_spec xs ys == 1) =
  assert_norm (find_bottom_spec xs ys == 1)
