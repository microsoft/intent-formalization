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

(* === Completeness (Appendix B): comparison count uniquely determined === *)
let test_min_complete (cf:nat) : Lemma
  (requires complexity_bounded_min cf 0 6)
  (ensures cf == 5) = ()

let test_max_complete (cf:nat) : Lemma
  (requires complexity_bounded_max cf 0 6)
  (ensures cf == 5) = ()

let test_min_trivial_complete (cf:nat) : Lemma
  (requires complexity_bounded_min cf 0 1)
  (ensures cf == 0) = ()
