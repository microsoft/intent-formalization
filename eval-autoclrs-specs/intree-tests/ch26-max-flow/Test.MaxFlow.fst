module Test.MaxFlow

open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq
open CLRS.Ch26.MaxFlow.Spec

(* Simple 2-node flow network: capacity(0→1)=10
   cap = [0; 10; 0; 0]  (2×2 flat)
   flow = [0; 5; 0; 0]  (flow of 5 from 0 to 1)
*)
let cap : capacity_matrix 2 = seq_of_list [0; 10; 0; 0]
let flow : flow_matrix 2 = seq_of_list [0; 5; 0; 0]

(* === Soundness: get element from matrices === *)
let test_get_cap () : Lemma (get cap 2 0 1 == 10) = ()
let test_get_flow () : Lemma (get flow 2 0 1 == 5) = ()

(* === Soundness: flow value = net flow out of source === *)
let test_flow_value () : Lemma (sum_flow_out flow 2 0 2 == 5) =
  assert_norm (sum_flow_out flow 2 0 2 == 5)

(* === Soundness: zero flow satisfies capacity constraint === *)
let zero_flow : flow_matrix 2 = seq_of_list [0; 0; 0; 0]

let test_zero_flow () : Lemma (valid_flow zero_flow cap 0 1) = ()


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_get_cap_complete (y:int) : Lemma
  (requires get cap 2 0 1 == y)
  (ensures y == 10) =
  ()

let test_get_flow_complete (y:int) : Lemma
  (requires get flow 2 0 1 == y)
  (ensures y == 5) =
  ()

let test_flow_value_complete (y:int) : Lemma
  (requires sum_flow_out flow 2 0 2 == y)
  (ensures y == 5) =
  assert_norm (sum_flow_out flow 2 0 2 == 5)
