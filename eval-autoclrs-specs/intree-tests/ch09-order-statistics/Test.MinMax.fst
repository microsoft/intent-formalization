module Test.MinMax

open CLRS.Ch09.MinMax.Spec

(* complexity_bounded_min(cf, c0, n) : cf >= c0 /\ cf - c0 == n - 1 *)

(* === Soundness: 6-element array needs exactly 5 comparisons === *)
let test_min_sound_1 () : Lemma (complexity_bounded_min 5 0 6) = ()
let test_min_sound_2 () : Lemma (complexity_bounded_min 8 3 6) = ()

(* === Soundness: max has same bound === *)
let test_max_sound_1 () : Lemma (complexity_bounded_max 5 0 6) = ()

(* === Soundness: 1-element needs 0 comparisons === *)
let test_min_trivial () : Lemma (complexity_bounded_min 0 0 1) = ()

(* === Completeness: too few comparisons === *)
[@@expect_failure]
let test_min_complete_1 () : Lemma (complexity_bounded_min 3 0 6) = ()

(* === Completeness: wrong offset === *)
[@@expect_failure]
let test_min_complete_2 () : Lemma (complexity_bounded_min 4 0 6) = ()
