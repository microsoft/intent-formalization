module Test.BucketSort

open FStar.List.Tot
open CLRS.Ch08.BucketSort.Spec

let test1 () : Lemma (insertion_sort [3; 1; 2] == [1; 2; 3]) =
  assert_norm (insertion_sort [3; 1; 2] == [1; 2; 3])
