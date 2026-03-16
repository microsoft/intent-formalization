(* Second completeness example — different input *)
module Test.RadixSort2

open CLRS.Ch08.RadixSort.Spec

let test2 () : Lemma (digit_sum 456 3 10 3 == 456) =
  digit_decomposition 456 3 10;
  assert_norm (digit_sum 456 3 10 3 == 456)
