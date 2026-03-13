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


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_complete_search_1 (y:bool) : Lemma
  (requires bst_search t 1 == y)
  (ensures y == true) =
  ()

let test_complete_search_2 (y:bool) : Lemma
  (requires bst_search t 2 == y)
  (ensures y == true) =
  ()

let test_complete_search_3 (y:bool) : Lemma
  (requires bst_search t 3 == y)
  (ensures y == true) =
  ()

let test_complete_valid (y:bool) : Lemma
  (requires bst_valid t == y)
  (ensures y == true) =
  ()

let test_complete_inorder (y:(list int)) : Lemma
  (requires bst_inorder t == y)
  (ensures y == [1; 2; 3]) =
  ()

let test_complete_delete (y:bool) : Lemma
  (requires bst_search t_del 2 == y)
  (ensures y == false) =
  ()
