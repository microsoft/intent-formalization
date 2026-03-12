module Test.MatrixMultiply

open FStar.Seq
open FStar.Mul
open CLRS.Ch04.MatrixMultiply.Spec

(* 2×2 matrices stored flat:
   A = [[1;2];[3;4]] → [1;2;3;4]
   B = [[5;6];[7;8]] → [5;6;7;8]
   C = A*B = [[19;22];[43;50]] → [19;22;43;50]
*)
let a : seq int = seq_of_list [1; 2; 3; 4]
let b : seq int = seq_of_list [5; 6; 7; 8]
let c : seq int = seq_of_list [19; 22; 43; 50]

(* === Soundness: flat_index === *)
let test_flat_idx () : Lemma (flat_index 2 0 0 == 0 /\ flat_index 2 0 1 == 1 /\
                              flat_index 2 1 0 == 2 /\ flat_index 2 1 1 == 3) = ()

(* === Soundness: dot_product_spec computes C[0][0] = 1*5 + 2*7 = 19 === *)
let test_dot_sound_1 () : Lemma (dot_product_spec a b 2 0 0 2 == 19) =
  assert_norm (dot_product_spec a b 2 0 0 2 == 19)

(* === Soundness: dot_product_spec computes C[1][1] = 3*6 + 4*8 = 50 === *)
let test_dot_sound_2 () : Lemma (dot_product_spec a b 2 1 1 2 == 50) =
  assert_norm (dot_product_spec a b 2 1 1 2 == 50)

(* === Soundness: full matrix multiply correctness === *)
let test_mat_mul_correct () : Lemma (mat_mul_correct a b c 2) = ()

(* === Completeness: wrong dot product === *)
[@@expect_failure]
let test_dot_complete () : Lemma (dot_product_spec a b 2 0 0 2 == 20) =
  assert_norm (dot_product_spec a b 2 0 0 2 == 20)

(* === Completeness: wrong matrix product === *)
let bad_c : seq int = seq_of_list [19; 22; 43; 51]

[@@expect_failure]
let test_mat_mul_complete () : Lemma (mat_mul_correct a b bad_c 2) = ()
