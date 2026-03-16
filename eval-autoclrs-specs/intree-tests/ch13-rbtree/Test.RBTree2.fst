module Test.RBTree2
(* Second completeness example — different input *)

open CLRS.Ch13.RBTree.Spec

(* === Soundness: insert into empty tree === *)
let t1 = insert Leaf 10

let test_insert_single () : Lemma (is_rbtree t1 = true) =
  assert_norm (is_rbtree t1 = true)

let test_search_found () : Lemma (search t1 10 == Some 10) =
  assert_norm (search t1 10 == Some 10)

let test_search_miss () : Lemma (search t1 8 == None) =
  assert_norm (search t1 8 == None)

(* === Soundness: insert multiple keys === *)
let t2 = insert t1 4
let t3 = insert t2 12

let test_rbtree_valid () : Lemma (is_rbtree t3 = true) =
  assert_norm (is_rbtree t3 = true)

let test_search_left () : Lemma (search t3 4 == Some 4) =
  assert_norm (search t3 4 == Some 4)

let test_search_right () : Lemma (search t3 12 == Some 12) =
  assert_norm (search t3 12 == Some 12)

let test_search_root () : Lemma (search t3 10 == Some 10) =
  assert_norm (search t3 10 == Some 10)

(* === Soundness: search not in tree === *)
let test_search_absent () : Lemma (search t3 6 == None) =
  assert_norm (search t3 6 == None)


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_insert_single_complete (y:bool) : Lemma
  (requires is_rbtree t1 = y)
  (ensures y = true) =
  assert_norm (is_rbtree t1 = true)

let test_search_found_complete (y:(option int)) : Lemma
  (requires search t1 10 == y)
  (ensures y == Some 10) =
  assert_norm (search t1 10 == Some 10)

let test_rbtree_valid_complete (y:bool) : Lemma
  (requires is_rbtree t3 = y)
  (ensures y = true) =
  assert_norm (is_rbtree t3 = true)

let test_search_left_complete (y:(option int)) : Lemma
  (requires search t3 4 == y)
  (ensures y == Some 4) =
  assert_norm (search t3 4 == Some 4)

let test_search_right_complete (y:(option int)) : Lemma
  (requires search t3 12 == y)
  (ensures y == Some 12) =
  assert_norm (search t3 12 == Some 12)

let test_search_root_complete (y:(option int)) : Lemma
  (requires search t3 10 == y)
  (ensures y == Some 10) =
  assert_norm (search t3 10 == Some 10)
