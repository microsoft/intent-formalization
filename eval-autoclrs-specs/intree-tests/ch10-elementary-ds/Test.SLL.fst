module Test.SLL

open FStar.List.Tot
open CLRS.Ch10.SinglyLinkedList.Spec

(* === Soundness: insert_head and search === *)
let l0 : list int = []
let l1 : list int = list_insert_head l0 3
let l2 : list int = list_insert_head l1 2
let l3 : list int = list_insert_head l2 1

let test_insert_sound () : Lemma (l3 == [1; 2; 3]) =
  assert_norm (l3 == [1; 2; 3])

let test_search_found () : Lemma (list_search l3 2 == true) =
  assert_norm (list_search l3 2 == true)

let test_search_not_found () : Lemma (list_search l3 4 == false) =
  assert_norm (list_search l3 4 == false)

(* === Soundness: delete === *)
let test_delete_sound () : Lemma (list_delete l3 2 == [1; 3]) =
  assert_norm (list_delete l3 2 == [1; 3])

(* === Completeness: wrong search === *)
[@@expect_failure]
let test_search_complete () : Lemma (list_search l3 4 == true) =
  assert_norm (list_search l3 4 == true)

(* === Completeness: wrong delete === *)
[@@expect_failure]
let test_delete_complete () : Lemma (list_delete l3 2 == [1; 2]) =
  assert_norm (list_delete l3 2 == [1; 2])
