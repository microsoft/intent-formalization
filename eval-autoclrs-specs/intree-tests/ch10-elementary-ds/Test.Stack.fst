module Test.Stack

open FStar.List.Tot
open CLRS.Ch10.Stack.Spec

(* === Soundness: push and pop === *)
let s0 : stack int = stack_empty
let s1 : stack int = stack_push s0 3
let s2 : stack int = stack_push s1 2
let s3 : stack int = stack_push s2 1

let test_push_sound () : Lemma (s3 == [1; 2; 3]) =
  assert_norm (s3 == [1; 2; 3])

let test_pop_sound_1 () : Lemma (stack_pop s3 == (1, [2; 3])) =
  assert_norm (stack_pop s3 == (1, [2; 3]))

let test_pop_sound_2 () : Lemma (stack_pop s1 == (3, [])) =
  assert_norm (stack_pop s1 == (3, []))

let test_empty_sound () : Lemma (stack_is_empty s0 == true) = ()
let test_nonempty_sound () : Lemma (stack_is_empty s3 == false) = ()
let test_size_sound () : Lemma (stack_size s3 == 3) = ()


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_push_complete (y:(list int)) : Lemma
  (requires s3 == y)
  (ensures y == [1; 2; 3]) =
  assert_norm (s3 == [1; 2; 3])

let test_empty_complete (y:bool) : Lemma
  (requires stack_is_empty s0 == y)
  (ensures y == true) =
  ()

let test_nonempty_complete (y:bool) : Lemma
  (requires stack_is_empty s3 == y)
  (ensures y == false) =
  ()

let test_size_complete (y:int) : Lemma
  (requires stack_size s3 == y)
  (ensures y == 3) =
  ()
