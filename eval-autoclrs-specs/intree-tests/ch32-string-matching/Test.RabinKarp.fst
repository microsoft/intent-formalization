module Test.RabinKarp

open FStar.Seq
open CLRS.Ch32.RabinKarp.Spec

let test1 () : Lemma (hash (seq_of_list [1; 2; 3]) 10 7 0 3 == 4) =
  assert_norm (hash (seq_of_list [1; 2; 3]) 10 7 0 3 == 4)
