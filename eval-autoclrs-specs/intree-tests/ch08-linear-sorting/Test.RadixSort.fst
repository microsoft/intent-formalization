module Test.RadixSort

open CLRS.Ch08.RadixSort.Spec

let test1 () : Lemma (digit_sum 123 3 10 3 == 123) =
  digit_decomposition 123 3 10;
  assert_norm (digit_sum 123 3 10 3 == 123)
