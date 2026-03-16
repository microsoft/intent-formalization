(* Second completeness example — different input *)
module Test.RabinKarp2

open FStar.Seq
open CLRS.Ch32.RabinKarp.Spec

let test2 () : Lemma (hash (seq_of_list [4; 5; 6]) 10 7 0 3 == 1) =
  assert_norm (hash (seq_of_list [4; 5; 6]) 10 7 0 3 == 1)
