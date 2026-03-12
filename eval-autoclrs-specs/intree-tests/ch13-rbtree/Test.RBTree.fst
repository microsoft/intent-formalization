module Test.RBTree

open CLRS.Ch13.RBTree.Spec

(* === Soundness: insert into empty tree === *)
let t1 = insert Leaf 5

let test_insert_single () : Lemma (is_rbtree t1 = true) =
  assert_norm (is_rbtree t1 = true)

let test_search_found () : Lemma (search t1 5 == Some 5) =
  assert_norm (search t1 5 == Some 5)

let test_search_miss () : Lemma (search t1 3 == None) =
  assert_norm (search t1 3 == None)

(* === Soundness: insert multiple keys === *)
let t2 = insert t1 3
let t3 = insert t2 7

let test_rbtree_valid () : Lemma (is_rbtree t3 = true) =
  assert_norm (is_rbtree t3 = true)

let test_search_left () : Lemma (search t3 3 == Some 3) =
  assert_norm (search t3 3 == Some 3)

let test_search_right () : Lemma (search t3 7 == Some 7) =
  assert_norm (search t3 7 == Some 7)

let test_search_root () : Lemma (search t3 5 == Some 5) =
  assert_norm (search t3 5 == Some 5)

(* === Soundness: search not in tree === *)
let test_search_absent () : Lemma (search t3 4 == None) =
  assert_norm (search t3 4 == None)

(* === Completeness: wrong search result === *)
[@@expect_failure]
let test_search_complete_1 () : Lemma (search t3 4 == Some 4) =
  assert_norm (search t3 4 == Some 4)

(* === Completeness: wrong RB tree validity === *)
let bad_tree = Node Red (Node Red Leaf 1 Leaf) 2 Leaf

[@@expect_failure]
let test_rbtree_complete () : Lemma (is_rbtree bad_tree = true) =
  assert_norm (is_rbtree bad_tree = true)
