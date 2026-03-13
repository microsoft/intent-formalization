module Test.Segments

open FStar.Mul
open CLRS.Ch33.Segments.Spec

(* === Soundness: cross product CCW === *)
(* (1-0)*(1-0) - (0-0)*(0-0) = 1 *)
let test_cross_sound_1 () : Lemma (cross_product_spec 0 0 1 0 0 1 == 1) = ()

(* === Soundness: cross product CW === *)
let test_cross_sound_2 () : Lemma (cross_product_spec 0 0 1 0 0 (-1) == -1) = ()

(* === Soundness: collinear points === *)
let test_cross_sound_3 () : Lemma (cross_product_spec 0 0 1 1 2 2 == 0) = ()

(* === Soundness: segments (0,0)-(2,0) and (1,-1)-(1,1) intersect === *)
let test_intersect_sound_1 () : Lemma (segments_intersect_spec 0 0 2 0 1 (-1) 1 1 == true) =
  assert_norm (segments_intersect_spec 0 0 2 0 1 (-1) 1 1 == true)

(* === Soundness: parallel non-intersecting segments === *)
let test_intersect_sound_2 () : Lemma (segments_intersect_spec 0 0 2 0 0 1 2 1 == false) =
  assert_norm (segments_intersect_spec 0 0 2 0 0 1 2 1 == false)

(* === Soundness: on_segment check === *)
let test_on_seg_sound () : Lemma (on_segment_spec 0 0 2 0 1 0 == true) = ()


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_cross_complete_1 (y:int) : Lemma
  (requires cross_product_spec 0 0 1 0 0 1 == y)
  (ensures y == 1) =
  ()

let test_cross_complete_2 (y:int) : Lemma
  (requires cross_product_spec 0 0 1 0 0 (-1) == y)
  (ensures y == -1) =
  ()

let test_cross_complete_3 (y:int) : Lemma
  (requires cross_product_spec 0 0 1 1 2 2 == y)
  (ensures y == 0) =
  ()

let test_intersect_complete_1 (y:bool) : Lemma
  (requires segments_intersect_spec 0 0 2 0 1 (-1) 1 1 == y)
  (ensures y == true) =
  assert_norm (segments_intersect_spec 0 0 2 0 1 (-1) 1 1 == true)

let test_intersect_complete_2 (y:bool) : Lemma
  (requires segments_intersect_spec 0 0 2 0 0 1 2 1 == y)
  (ensures y == false) =
  assert_norm (segments_intersect_spec 0 0 2 0 0 1 2 1 == false)

let test_on_seg_complete (y:bool) : Lemma
  (requires on_segment_spec 0 0 2 0 1 0 == y)
  (ensures y == true) =
  ()
