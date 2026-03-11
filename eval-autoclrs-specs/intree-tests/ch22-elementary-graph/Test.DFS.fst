module Test.DFS

open FStar.Mul
open FStar.Seq
open CLRS.Ch22.DFS.Spec

(* === Soundness: initial state === *)
let st0 = init_state 3

let test_init_time () : Lemma (st0.time == 0) = ()
let test_init_n () : Lemma (st0.n == 3) = ()

let test_init_colors () : Lemma (
  Seq.index st0.color 0 == White /\
  Seq.index st0.color 1 == White /\
  Seq.index st0.color 2 == White
) = ()

(* === Soundness: discover vertex 0 === *)
let st1 = discover_vertex 0 st0

let test_discover_color () : Lemma (Seq.index st1.color 0 == Gray) =
  assert_norm (Seq.index st1.color 0 == Gray)

let test_discover_time () : Lemma (st1.time == 1) =
  assert_norm (st1.time == 1)

(* === Soundness: undiscovered vertex stays White === *)
let test_other_unchanged () : Lemma (Seq.index st1.color 1 == White) =
  assert_norm (Seq.index st1.color 1 == White)

(* === Completeness: wrong color after discover === *)
[@@expect_failure]
let test_color_complete () : Lemma (Seq.index st1.color 0 == Black) =
  assert_norm (Seq.index st1.color 0 == Black)
