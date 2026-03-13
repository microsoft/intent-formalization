module Test.Queue

open FStar.List.Tot
open CLRS.Ch10.Queue.Spec

(* === Soundness: enqueue and dequeue (FIFO) === *)
let q0 : wf_queue int = queue_empty
let q1 = queue_enqueue q0 1
let q2 = queue_enqueue q1 2
let q3 = queue_enqueue q2 3

let test_to_list_sound () : Lemma (queue_to_list q3 == [1; 2; 3]) =
  assert_norm (queue_to_list q3 == [1; 2; 3])

let test_dequeue_sound () : Lemma (
  Some? (queue_dequeue q3) /\ fst (Some?.v (queue_dequeue q3)) == 1
) = assert_norm (
  Some? (queue_dequeue q3) /\ fst (Some?.v (queue_dequeue q3)) == 1)

let test_empty_sound () : Lemma (queue_is_empty q0 == true) = ()
let test_nonempty_sound () : Lemma (queue_is_empty q3 == false) = ()
let test_size_sound () : Lemma (queue_size q3 == 3) = ()

(* === Soundness: dequeue from empty returns None === *)
let test_dequeue_empty () : Lemma (queue_dequeue #int queue_empty == None) = ()


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_to_list_complete (y:(list int)) : Lemma
  (requires queue_to_list q3 == y)
  (ensures y == [1; 2; 3]) =
  assert_norm (queue_to_list q3 == [1; 2; 3])

let test_dequeue_complete (y:int) : Lemma
  (requires Some? (queue_dequeue q3) /\ fst (Some?.v (queue_dequeue q3)) == y)
  (ensures y == 1) =
  assert_norm (Some? (queue_dequeue q3) /\ fst (Some?.v (queue_dequeue q3)) == 1)

let test_empty_complete (y:bool) : Lemma
  (requires queue_is_empty q0 == y)
  (ensures y == true) =
  ()

let test_nonempty_complete (y:bool) : Lemma
  (requires queue_is_empty q3 == y)
  (ensures y == false) =
  ()

let test_size_complete (y:int) : Lemma
  (requires queue_size q3 == y)
  (ensures y == 3) =
  ()
