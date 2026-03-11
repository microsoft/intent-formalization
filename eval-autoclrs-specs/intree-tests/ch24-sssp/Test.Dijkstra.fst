module Test.Dijkstra

friend CLRS.Ch24.ShortestPath.Inf

open FStar.Mul
open CLRS.Ch24.ShortestPath.Inf
open CLRS.Ch24.ShortestPath.Spec

module Seq = FStar.Seq

(* 2-node graph: 0 --5--> 1, adjacency matrix [0, 5; inf, 0] *)
let adj : Seq.seq int = Seq.seq_of_list [0; 5; inf; 0]

(* === Soundness: sp_dist(0, 0) == 0 (source to self) === *)
let test_sound_self () : Lemma (sp_dist adj 2 0 0 == 0) =
  assert_norm (sp_dist_k adj 2 0 0 0 == 0)

(* === Soundness: sp_dist(0, 1) == 5 === *)
#push-options "--z3rlimit 100 --fuel 4 --ifuel 4"
let test_sound_dist () : Lemma (sp_dist adj 2 0 1 == 5) =
  assert_norm (sp_dist adj 2 0 1 == 5)
#pop-options

(* 3-node graph: 0 --1--> 1 --2--> 2, 0 --4--> 2 direct *)
let adj3 : Seq.seq int = Seq.seq_of_list [0; 1; 4; inf; 0; 2; inf; inf; 0]

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"
let test_sound_3node () : Lemma
  (sp_dist adj3 3 0 0 == 0 /\
   sp_dist adj3 3 0 1 == 1 /\
   sp_dist adj3 3 0 2 == 3)
= assert_norm (sp_dist adj3 3 0 0 == 0);
  assert_norm (sp_dist adj3 3 0 1 == 1);
  assert_norm (sp_dist adj3 3 0 2 == 3)
#pop-options

(* === Completeness: wrong distance must fail === *)
[@@expect_failure]
let test_complete_dist () : Lemma (sp_dist adj 2 0 1 == 3) =
  assert_norm (sp_dist adj 2 0 1 == 3)
