module Test.BSTArray

open FStar.Seq
open FStar.Mul
open CLRS.Ch12.BSTArray.Spec

(* pure_search normalization limited to base cases due to complex
   decreases clause. Test boundary/base-case behavior. *)

(* === Soundness: search on empty tree returns None === *)
let empty_keys : seq int = Seq.empty
let empty_valid : seq bool = Seq.empty

let test_search_empty () : Lemma (pure_search empty_keys empty_valid 0 0 5 == None) =
  assert_norm (pure_search empty_keys empty_valid 0 0 5 == None)

(* === Soundness: search beyond capacity returns None === *)
let keys1 : seq int = seq_of_list [5]
let valid1 : seq bool = seq_of_list [true]

let test_search_beyond_cap () : Lemma (pure_search keys1 valid1 0 0 5 == None) =
  assert_norm (pure_search keys1 valid1 0 0 5 == None)

(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_search_empty_complete (y:option nat) : Lemma
  (requires pure_search empty_keys empty_valid 0 0 5 == y)
  (ensures y == None) =
  assert_norm (pure_search empty_keys empty_valid 0 0 5 == None)

let test_search_beyond_complete (y:option nat) : Lemma
  (requires pure_search keys1 valid1 0 0 5 == y)
  (ensures y == None) =
  assert_norm (pure_search keys1 valid1 0 0 5 == None)
