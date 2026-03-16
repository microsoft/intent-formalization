module Test.KMP

open FStar.Seq
open CLRS.Ch32.KMP.Spec

let test1 () : Lemma (matched_prefix_at (seq_of_list [1; 2; 1; 2; 3]) (seq_of_list [1; 2]) 2 2) =
  assert_norm (matched_prefix_at (seq_of_list [1; 2; 1; 2; 3]) (seq_of_list [1; 2]) 2 2)
