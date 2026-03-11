module Test.FloydWarshall

open FStar.Mul
open FStar.Seq
open CLRS.Ch25.FloydWarshall.Spec

(* 2-node graph: 0 --3--> 1, no 1-->0 edge *)
let adj2 : seq int = seq_of_list [0; 3; inf; 0]

(* === Soundness: fw_outer computes APSP correctly === *)
let test_sound_2x2 () : Lemma
  (let r = fw_outer adj2 2 0 in
   index r 0 == 0 /\ index r 1 == 3 /\ index r 2 == inf /\ index r 3 == 0)
= assert_norm (index (fw_outer adj2 2 0) 0 == 0);
  assert_norm (index (fw_outer adj2 2 0) 1 == 3);
  assert_norm (index (fw_outer adj2 2 0) 2 == inf);
  assert_norm (index (fw_outer adj2 2 0) 3 == 0)

(* 3-node graph: 0 --2--> 1 --3--> 2, no other edges *)
let adj3 : seq int = seq_of_list [0; 2; inf; inf; 0; 3; inf; inf; 0]

(* Use fw_entry (recurrence) instead of fw_outer for 3x3 — avoids seq mutation overhead *)
#push-options "--z3rlimit 100"
let test_sound_3x3 () : Lemma
  (fw_entry adj3 3 0 0 3 == 0 /\
   fw_entry adj3 3 0 1 3 == 2 /\
   fw_entry adj3 3 0 2 3 == 5)
= assert_norm (fw_entry adj3 3 0 0 3 == 0);
  assert_norm (fw_entry adj3 3 0 1 3 == 2);
  assert_norm (fw_entry adj3 3 0 2 3 == 5)
#pop-options

(* === Completeness: wrong distance must fail === *)
[@@expect_failure]
let test_complete () : Lemma
  (let r = fw_outer adj2 2 0 in index r 1 == 4)
= assert_norm (index (fw_outer adj2 2 0) 1 == 4)
