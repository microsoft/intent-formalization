module Test.DLL

open FStar.List.Tot
open CLRS.Ch10.DLL.Spec

(* === Soundness: insert and search === *)
let l1 : dll_spec = dll_insert dll_empty 3
let l2 : dll_spec = dll_insert l1 2
let l3 : dll_spec = dll_insert l2 1

let test_insert_sound () : Lemma (l3 == [1; 2; 3]) =
  assert_norm (l3 == [1; 2; 3])

let test_search_found () : Lemma (dll_search l3 2 == true) =
  assert_norm (dll_search l3 2 == true)

let test_search_not_found () : Lemma (dll_search l3 4 == false) =
  assert_norm (dll_search l3 4 == false)

(* === Soundness: delete === *)
let test_delete_sound () : Lemma (dll_delete l3 2 == [1; 3]) =
  assert_norm (dll_delete l3 2 == [1; 3])


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_insert_complete (y:(list int)) : Lemma
  (requires l3 == y)
  (ensures y == [1; 2; 3]) =
  assert_norm (l3 == [1; 2; 3])

let test_search_found_complete (y:bool) : Lemma
  (requires dll_search l3 2 == y)
  (ensures y == true) =
  assert_norm (dll_search l3 2 == true)

let test_search_not_found_complete (y:bool) : Lemma
  (requires dll_search l3 4 == y)
  (ensures y == false) =
  assert_norm (dll_search l3 4 == false)

let test_delete_complete (y:(list int)) : Lemma
  (requires dll_delete l3 2 == y)
  (ensures y == [1; 3]) =
  assert_norm (dll_delete l3 2 == [1; 3])
