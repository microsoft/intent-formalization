module Test.BST

open CLRS.Ch12.BST.Spec

let t : bst = bst_insert (bst_insert (bst_insert Leaf 2) 1) 3

(* === Soundness: search finds inserted keys === *)
let test_sound_search_1 () : Lemma (bst_search t 1 == true) = ()
let test_sound_search_2 () : Lemma (bst_search t 2 == true) = ()
let test_sound_search_3 () : Lemma (bst_search t 3 == true) = ()

(* === Soundness: valid BST after insertions === *)
let test_sound_valid () : Lemma (bst_valid t == true) = ()

(* === Soundness: inorder gives sorted list === *)
let test_sound_inorder () : Lemma (bst_inorder t == [1; 2; 3]) = ()

(* === Soundness: delete removes key === *)
let t_del : bst = bst_delete t 2
let test_sound_delete () : Lemma (bst_search t_del 2 == false) = ()
let test_sound_delete_keeps () : Lemma (bst_search t_del 1 == true /\ bst_search t_del 3 == true) = ()

(* === Completeness: search for missing key must fail === *)
[@@expect_failure]
let test_complete_search () : Lemma (bst_search t 4 == true) = ()

(* === Completeness: wrong inorder must fail === *)
[@@expect_failure]
let test_complete_inorder () : Lemma (bst_inorder t == [2; 1; 3]) = ()
