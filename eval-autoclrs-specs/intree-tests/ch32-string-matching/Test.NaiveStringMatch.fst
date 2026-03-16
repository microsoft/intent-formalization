module Test.NaiveStringMatch

open FStar.Seq
open CLRS.Ch32.NaiveStringMatch.Spec

let test1 () : Lemma (matches_at_dec (seq_of_list [1; 2; 1; 2; 3]) (seq_of_list [1; 2]) 0 == true) =
  assert_norm (matches_at_dec (seq_of_list [1; 2; 1; 2; 3]) (seq_of_list [1; 2]) 0 == true)
