module Test.SimultaneousMinMax

open CLRS.Ch09.SimultaneousMinMax.Spec

(* complexity_bounded_minmax(cf, c0, n) : cf >= c0 /\ cf - c0 == 2*(n-1)
   complexity_bounded_minmax_pairs(cf, c0, n) : 2*(cf-c0) <= 3*n *)

(* === Soundness: 8-element array, simple scan needs 2*(8-1)=14 comparisons === *)
let test_simple_sound_1 () : Lemma (complexity_bounded_minmax 14 0 8) = ()

(* === Soundness: with nonzero c0 === *)
let test_simple_sound_2 () : Lemma (complexity_bounded_minmax 19 5 8) = ()

(* === Soundness: pair processing bound === *)
let test_pairs_sound_1 () : Lemma (complexity_bounded_minmax_pairs 12 0 8) = ()

(* === Completeness (Appendix B): comparison count uniquely determined === *)
let test_simple_complete (cf:nat) : Lemma
  (requires complexity_bounded_minmax cf 0 8)
  (ensures cf == 14) = ()

(* Note: complexity_bounded_minmax_pairs uses inequality (<=), so multiple
   cf values satisfy it — completeness is intentionally not provable,
   demonstrating the bound is not tight. *)
