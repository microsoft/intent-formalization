module Test.MatrixChain

open FStar.Seq
open FStar.Mul
open CLRS.Ch15.MatrixChain.Spec

(* Matrix chain: dims = [10; 20; 30] means 2 matrices: 10×20 and 20×30
   Optimal cost: 10*20*30 = 6000 (only one way to multiply 2 matrices)
*)

let dims : seq int = seq_of_list [10; 20; 30]
let init_table : seq int = seq_of_list [0; 0; 0; 0]

(* === Soundness: mc_inner_k computes cost of single split === *)
let test_inner_k_sound () : Lemma (mc_inner_k init_table dims 2 0 1 0 1000000000 == 6000) =
  assert_norm (mc_inner_k init_table dims 2 0 1 0 1000000000 == 6000)


(* === Completeness (Appendix B): spec uniquely determines output === *)
let test_inner_k_complete (y:int) : Lemma
  (requires mc_inner_k init_table dims 2 0 1 0 1000000000 == y)
  (ensures y == 6000) =
  assert_norm (mc_inner_k init_table dims 2 0 1 0 1000000000 == 6000)
