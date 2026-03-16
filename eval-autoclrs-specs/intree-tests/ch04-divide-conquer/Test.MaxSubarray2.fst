(* Second completeness example — different input *)
module Test.MaxSubarray2

open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec

let test3 () : Lemma (max_subarray_spec (seq_of_list [(-1); 3; (-2); 5; (-1)]) == 6) =
  assert_norm (max_subarray_spec (seq_of_list [(-1); 3; (-2); 5; (-1)]) == 6)
