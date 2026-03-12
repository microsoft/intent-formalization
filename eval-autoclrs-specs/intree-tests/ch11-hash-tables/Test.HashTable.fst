module Test.HashTable

open CLRS.Ch11.HashTable.Spec

(* === Soundness: insert and search === *)
let m1 : ht_model = ht_insert ht_empty 1 10
let m2 : ht_model = ht_insert m1 2 20
let m3 : ht_model = ht_insert m2 3 30

let test_search_found_1 () : Lemma (ht_search m3 1 == Some 10) =
  assert_norm (ht_search m3 1 == Some 10)

let test_search_found_2 () : Lemma (ht_search m3 3 == Some 30) =
  assert_norm (ht_search m3 3 == Some 30)

let test_search_not_found () : Lemma (ht_search m3 4 == None) =
  assert_norm (ht_search m3 4 == None)

(* === Soundness: delete === *)
let m4 : ht_model = ht_delete m3 2

let test_delete_search () : Lemma (ht_search m4 2 == None) =
  assert_norm (ht_search m4 2 == None)

(* === Soundness: search after delete preserves others === *)
let test_delete_preserves () : Lemma (ht_search m4 1 == Some 10) =
  assert_norm (ht_search m4 1 == Some 10)

(* === Completeness: wrong search result === *)
[@@expect_failure]
let test_search_complete () : Lemma (ht_search m3 1 == Some 20) =
  assert_norm (ht_search m3 1 == Some 20)

(* === Completeness: found after delete === *)
[@@expect_failure]
let test_delete_complete () : Lemma (ht_search m4 2 == Some 20) =
  assert_norm (ht_search m4 2 == Some 20)
