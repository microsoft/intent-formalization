(* Second completeness example — different input *)
module Test.KMP2

open FStar.Seq
open CLRS.Ch32.KMP.Spec

let test2 () : Lemma (matched_prefix_at (seq_of_list [3; 1; 2; 3; 1]) (seq_of_list [3; 1]) 0 2) =
  assert_norm (matched_prefix_at (seq_of_list [3; 1; 2; 3; 1]) (seq_of_list [3; 1]) 0 2)
