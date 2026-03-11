module Test.JarvisMarch

open FStar.Mul
module Seq = FStar.Seq
open CLRS.Ch33.Segments.Spec
open CLRS.Ch33.JarvisMarch.Spec

(* Points: (0,0), (2,0), (1,2), (1,1)
   xs = [0; 2; 1; 1], ys = [0; 0; 2; 1] *)
let xs : Seq.seq int = Seq.seq_of_list [0; 2; 1; 1]
let ys : Seq.seq int = Seq.seq_of_list [0; 0; 2; 1]

(* === Soundness: find_leftmost returns index of min-x point === *)
(* Point 0 has x=0 (smallest) → index 0 *)
let test_leftmost () : Lemma (find_leftmost_spec xs ys == 0) =
  assert_norm (find_leftmost_spec xs ys == 0)

(* === Soundness: with different leftmost point === *)
let xs2 : Seq.seq int = Seq.seq_of_list [3; 1; 2]
let ys2 : Seq.seq int = Seq.seq_of_list [0; 0; 0]

let test_leftmost_2 () : Lemma (find_leftmost_spec xs2 ys2 == 1) =
  assert_norm (find_leftmost_spec xs2 ys2 == 1)

(* === Completeness: wrong leftmost === *)
[@@expect_failure]
let test_leftmost_complete () : Lemma (find_leftmost_spec xs ys == 1) =
  assert_norm (find_leftmost_spec xs ys == 1)
