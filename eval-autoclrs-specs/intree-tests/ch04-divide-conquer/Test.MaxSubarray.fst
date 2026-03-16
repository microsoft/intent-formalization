module Test.MaxSubarray

open FStar.Seq
open CLRS.Ch04.MaxSubarray.Spec

let test1 () : Lemma (max_subarray_spec (seq_of_list [(-1); 3; (-2)]) == 3) =
  assert_norm (max_subarray_spec (seq_of_list [(-1); 3; (-2)]) == 3)

let test2 () : Lemma (max_subarray_spec (seq_of_list [1; 2; 3]) == 6) =
  assert_norm (max_subarray_spec (seq_of_list [1; 2; 3]) == 6)
