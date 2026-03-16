(* Second completeness example — different input *)
module Test.NaiveStringMatch2

open FStar.Seq
open CLRS.Ch32.NaiveStringMatch.Spec

let test2 () : Lemma (matches_at_dec (seq_of_list [3; 1; 2; 4]) (seq_of_list [1; 2]) 1 == true) =
  assert_norm (matches_at_dec (seq_of_list [3; 1; 2; 4]) (seq_of_list [1; 2]) 1 == true)

let test2_no_match () : Lemma (matches_at_dec (seq_of_list [3; 1; 2; 4]) (seq_of_list [1; 2]) 0 == false) =
  assert_norm (matches_at_dec (seq_of_list [3; 1; 2; 4]) (seq_of_list [1; 2]) 0 == false)
