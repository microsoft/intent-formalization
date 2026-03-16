(* Second completeness example — different input *)
module Test.BucketSort2

open FStar.List.Tot
open CLRS.Ch08.BucketSort.Spec

let test2 () : Lemma (insertion_sort [5; 1; 4; 2] == [1; 2; 4; 5]) =
  assert_norm (insertion_sort [5; 1; 4; 2] == [1; 2; 4; 5])
