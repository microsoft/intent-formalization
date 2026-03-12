module Test.InsertionSort

(* Appendix B Completeness Check (FMCAD 2024):
   For spec phi(x,y) = sorted(y) /\ permutation(x,y):
     Soundness:    phi(input, expected) holds
     Completeness: phi(input, y) ==> y == expected *)

module Seq = FStar.Seq
open Pulse.Lib.BoundedIntegers
open CLRS.Common.SortSpec

(* Helper: unfold Seq.count for length-3 sequences *)
#push-options "--fuel 3 --ifuel 1 --z3rlimit 200"
private let count3 (x:int) (s:Seq.seq int) : Lemma
  (requires Seq.length s == 3)
  (ensures Seq.count x s ==
    (if Seq.index s 0 = x then 1 else 0) +
    (if Seq.index s 1 = x then 1 else 0) +
    (if Seq.index s 2 = x then 1 else 0)) =
  let t1 = Seq.tail s in
  assert (Seq.length t1 == 2);
  assert (Seq.head s == Seq.index s 0);
  Seq.lemma_index_slice s 1 3 0;
  assert (Seq.index t1 0 == Seq.index s 1);
  assert (Seq.head t1 == Seq.index t1 0);
  let t2 = Seq.tail t1 in
  assert (Seq.length t2 == 1);
  Seq.lemma_index_slice t1 1 2 0;
  Seq.lemma_index_slice s 1 3 1;
  assert (Seq.index t2 0 == Seq.index s 2);
  assert (Seq.head t2 == Seq.index t2 0);
  let t3 = Seq.tail t2 in
  assert (Seq.length t3 == 0);
  assert (Seq.count x t3 == 0);
  assert (Seq.count x t2 == (if Seq.index s 2 = x then 1 else 0));
  assert (Seq.count x t1 ==
    (if Seq.index s 1 = x then 1 else 0) +
    (if Seq.index s 2 = x then 1 else 0));
  ()
#pop-options

(* Helper: unfold Seq.count for length-2 sequences *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 100"
private let count2 (x:int) (s:Seq.seq int) : Lemma
  (requires Seq.length s == 2)
  (ensures Seq.count x s ==
    (if Seq.index s 0 = x then 1 else 0) +
    (if Seq.index s 1 = x then 1 else 0)) =
  let t1 = Seq.tail s in
  assert (Seq.length t1 == 1);
  assert (Seq.head s == Seq.index s 0);
  Seq.lemma_index_slice s 1 2 0;
  assert (Seq.index t1 0 == Seq.index s 1);
  assert (Seq.head t1 == Seq.index t1 0);
  let t2 = Seq.tail t1 in
  assert (Seq.length t2 == 0);
  assert (Seq.count x t2 == 0);
  assert (Seq.count x t1 == (if Seq.index s 1 = x then 1 else 0));
  ()
#pop-options

(* === Test case 1: [3; 1; 2] === *)
let i1 : Seq.seq int = Seq.seq_of_list [3; 1; 2]
let o1 : Seq.seq int = Seq.seq_of_list [1; 2; 3]

let test_sound_1 () : Lemma (sorted o1 /\ permutation i1 o1) =
  reveal_opaque (`%permutation) (permutation i1 o1)

#push-options "--z3rlimit 600"
let test_complete_1 (y: Seq.seq int) : Lemma
  (requires sorted y /\ permutation i1 y)
  (ensures y == o1) =
  reveal_opaque (`%permutation) (permutation i1 y);
  assert (Seq.length y == 3);
  (* Expand count on y for values 1, 2, 3 *)
  count3 1 y; count3 2 y; count3 3 y;
  assert_norm (Seq.count 1 i1 == 1);
  assert_norm (Seq.count 2 i1 == 1);
  assert_norm (Seq.count 3 i1 == 1);
  (* Expand count of y[j] on i1 -- establishes y[j] in {1,2,3} *)
  count3 (Seq.index y 0) i1;
  count3 (Seq.index y 1) i1;
  count3 (Seq.index y 2) i1;
  assert_norm (Seq.index i1 0 == 3);
  assert_norm (Seq.index i1 1 == 1);
  assert_norm (Seq.index i1 2 == 2);
  (* self-count: count(y[j], y) >= 1 *)
  count3 (Seq.index y 0) y;
  count3 (Seq.index y 1) y;
  count3 (Seq.index y 2) y;
  (* Explicit membership for SMT *)
  assert (Seq.index y 0 = 1 \/ Seq.index y 0 = 2 \/ Seq.index y 0 = 3);
  assert (Seq.index y 1 = 1 \/ Seq.index y 1 = 2 \/ Seq.index y 1 = 3);
  assert (Seq.index y 2 = 1 \/ Seq.index y 2 = 2 \/ Seq.index y 2 = 3);
  (* Step-by-step derivation *)
  (* Instantiate sorted for adjacent pairs *)
  assert (Seq.index y 0 <= Seq.index y 1);
  assert (Seq.index y 1 <= Seq.index y 2);
  assert (Seq.index y 0 = 1);
  (* count(1,y)=1 and y[0]=1 implies y[1]<>1 and y[2]<>1 *)
  assert (Seq.index y 1 <> 1);
  assert (Seq.index y 2 <> 1);
  (* y[1] in {2,3}, y[2] in {2,3} *)
  (* Simplify count(2,y) with y[0]=1: *)
  assert ((if Seq.index y 1 = 2 then 1 else 0) + (if Seq.index y 2 = 2 then 1 else 0) == 1);
  (* If y[2]=2, sorted forces y[1]<=2, so y[1]=2, then count(2)=2, contradiction *)
  assert (Seq.index y 2 <> 2);
  assert (Seq.index y 2 = 3);
  (* count(3,y)=1 and y[2]=3 implies y[1]<>3 *)
  assert (Seq.index y 1 <> 3);
  (* y[1] in {2,3} \ {3} = {2} *)
  assert (Seq.index y 1 = 2);
  Seq.lemma_eq_elim y o1
#pop-options

(* === Test case 2: [5; 3; 1; 4; 2] === *)
let i2 : Seq.seq int = Seq.seq_of_list [5; 3; 1; 4; 2]
let o2 : Seq.seq int = Seq.seq_of_list [1; 2; 3; 4; 5]

#push-options "--z3rlimit 100"
let test_sound_2 () : Lemma (sorted o2 /\ permutation i2 o2) =
  reveal_opaque (`%permutation) (permutation i2 o2)
#pop-options

(* Helper: unfold Seq.count for length-5 sequences *)
#push-options "--fuel 5 --ifuel 1 --z3rlimit 400"
private let count5 (x:int) (s:Seq.seq int) : Lemma
  (requires Seq.length s == 5)
  (ensures Seq.count x s ==
    (if Seq.index s 0 = x then 1 else 0) +
    (if Seq.index s 1 = x then 1 else 0) +
    (if Seq.index s 2 = x then 1 else 0) +
    (if Seq.index s 3 = x then 1 else 0) +
    (if Seq.index s 4 = x then 1 else 0)) =
  let n = 5 in
  let t1 = Seq.tail s in
  assert (Seq.length t1 == 4);
  assert (Seq.head s == Seq.index s 0);
  Seq.lemma_index_slice s 1 n 0;
  Seq.lemma_index_slice s 1 n 1;
  Seq.lemma_index_slice s 1 n 2;
  Seq.lemma_index_slice s 1 n 3;
  assert (Seq.index t1 0 == Seq.index s 1);
  assert (Seq.index t1 1 == Seq.index s 2);
  assert (Seq.index t1 2 == Seq.index s 3);
  assert (Seq.index t1 3 == Seq.index s 4);
  let t2 = Seq.tail t1 in
  assert (Seq.length t2 == 3);
  Seq.lemma_index_slice t1 1 4 0;
  Seq.lemma_index_slice t1 1 4 1;
  Seq.lemma_index_slice t1 1 4 2;
  assert (Seq.index t2 0 == Seq.index s 2);
  assert (Seq.index t2 1 == Seq.index s 3);
  assert (Seq.index t2 2 == Seq.index s 4);
  let t3 = Seq.tail t2 in
  assert (Seq.length t3 == 2);
  Seq.lemma_index_slice t2 1 3 0;
  Seq.lemma_index_slice t2 1 3 1;
  assert (Seq.index t3 0 == Seq.index s 3);
  assert (Seq.index t3 1 == Seq.index s 4);
  let t4 = Seq.tail t3 in
  assert (Seq.length t4 == 1);
  Seq.lemma_index_slice t3 1 2 0;
  assert (Seq.index t4 0 == Seq.index s 4);
  let t5 = Seq.tail t4 in
  assert (Seq.length t5 == 0);
  assert (Seq.count x t5 == 0);
  assert (Seq.count x t4 == (if Seq.index s 4 = x then 1 else 0));
  assert (Seq.count x t3 ==
    (if Seq.index s 3 = x then 1 else 0) +
    (if Seq.index s 4 = x then 1 else 0));
  assert (Seq.count x t2 ==
    (if Seq.index s 2 = x then 1 else 0) +
    (if Seq.index s 3 = x then 1 else 0) +
    (if Seq.index s 4 = x then 1 else 0));
  assert (Seq.count x t1 ==
    (if Seq.index s 1 = x then 1 else 0) +
    (if Seq.index s 2 = x then 1 else 0) +
    (if Seq.index s 3 = x then 1 else 0) +
    (if Seq.index s 4 = x then 1 else 0));
  ()
#pop-options

#push-options "--fuel 5 --z3rlimit 1200"
let test_complete_2 (y: Seq.seq int) : Lemma
  (requires sorted y /\ permutation i2 y)
  (ensures y == o2) =
  reveal_opaque (`%permutation) (permutation i2 y);
  assert (Seq.length y == 5);
  (* Expand count on y for each distinct value *)
  count5 1 y; count5 2 y; count5 3 y; count5 4 y; count5 5 y;
  assert_norm (Seq.count 1 i2 == 1);
  assert_norm (Seq.count 2 i2 == 1);
  assert_norm (Seq.count 3 i2 == 1);
  assert_norm (Seq.count 4 i2 == 1);
  assert_norm (Seq.count 5 i2 == 1);
  (* Expand count of y[j] on i2 — establishes y[j] in {1..5} *)
  count5 (Seq.index y 0) i2;
  count5 (Seq.index y 1) i2;
  count5 (Seq.index y 2) i2;
  count5 (Seq.index y 3) i2;
  count5 (Seq.index y 4) i2;
  assert_norm (Seq.index i2 0 == 5);
  assert_norm (Seq.index i2 1 == 3);
  assert_norm (Seq.index i2 2 == 1);
  assert_norm (Seq.index i2 3 == 4);
  assert_norm (Seq.index i2 4 == 2);
  (* Self-count: count(y[j], y) >= 1 *)
  count5 (Seq.index y 0) y;
  count5 (Seq.index y 1) y;
  count5 (Seq.index y 2) y;
  count5 (Seq.index y 3) y;
  count5 (Seq.index y 4) y;
  (* Explicit membership *)
  assert (Seq.index y 0 = 1 \/ Seq.index y 0 = 2 \/ Seq.index y 0 = 3 \/ Seq.index y 0 = 4 \/ Seq.index y 0 = 5);
  assert (Seq.index y 1 = 1 \/ Seq.index y 1 = 2 \/ Seq.index y 1 = 3 \/ Seq.index y 1 = 4 \/ Seq.index y 1 = 5);
  assert (Seq.index y 2 = 1 \/ Seq.index y 2 = 2 \/ Seq.index y 2 = 3 \/ Seq.index y 2 = 4 \/ Seq.index y 2 = 5);
  assert (Seq.index y 3 = 1 \/ Seq.index y 3 = 2 \/ Seq.index y 3 = 3 \/ Seq.index y 3 = 4 \/ Seq.index y 3 = 5);
  assert (Seq.index y 4 = 1 \/ Seq.index y 4 = 2 \/ Seq.index y 4 = 3 \/ Seq.index y 4 = 4 \/ Seq.index y 4 = 5);
  (* Step-by-step derivation from sorted + count=1 *)
  assert (Seq.index y 0 <= Seq.index y 1);
  assert (Seq.index y 1 <= Seq.index y 2);
  assert (Seq.index y 2 <= Seq.index y 3);
  assert (Seq.index y 3 <= Seq.index y 4);
  assert (Seq.index y 0 = 1);
  assert (Seq.index y 1 <> 1);
  assert (Seq.index y 2 <> 1);
  assert (Seq.index y 3 <> 1);
  assert (Seq.index y 4 <> 1);
  assert (Seq.index y 4 = 5);
  assert (Seq.index y 3 <> 5);
  assert (Seq.index y 2 <> 5);
  assert (Seq.index y 1 <> 5);
  (* y[1] in {2,3,4}: if y[1]>=3 then y[2],y[3]>=3, no room for 2 in y[1..3] *)
  assert ((if Seq.index y 1 = 2 then 1 else 0) + (if Seq.index y 2 = 2 then 1 else 0) +
          (if Seq.index y 3 = 2 then 1 else 0) + (if Seq.index y 4 = 2 then 1 else 0) == 1);
  assert (Seq.index y 1 = 2);
  assert (Seq.index y 2 <> 2);
  assert (Seq.index y 3 <> 2);
  (* y[3] in {3,4}: if y[3]=3 then y[2]<=3, y[2] in {3,4}\{2,5,1}, but need count(4)=1
     y[2] in {3}, count(3) would be 2 (y[2]=3 and y[3]=3), contradiction *)
  assert ((if Seq.index y 2 = 4 then 1 else 0) + (if Seq.index y 3 = 4 then 1 else 0) == 1);
  assert (Seq.index y 3 = 4);
  assert (Seq.index y 2 <> 4);
  assert (Seq.index y 2 = 3);
  Seq.lemma_eq_elim y o2
#pop-options

(* === Test case 3: [2; 1] === *)
let i3 : Seq.seq int = Seq.seq_of_list [2; 1]
let o3 : Seq.seq int = Seq.seq_of_list [1; 2]

let test_sound_3 () : Lemma (sorted o3 /\ permutation i3 o3) =
  reveal_opaque (`%permutation) (permutation i3 o3)

#push-options "--z3rlimit 600"
let test_complete_3 (y: Seq.seq int) : Lemma
  (requires sorted y /\ permutation i3 y)
  (ensures y == o3) =
  reveal_opaque (`%permutation) (permutation i3 y);
  assert (Seq.length y == 2);
  count2 1 y; count2 2 y;
  assert_norm (Seq.count 1 i3 == 1);
  assert_norm (Seq.count 2 i3 == 1);
  count2 (Seq.index y 0) i3;
  count2 (Seq.index y 1) i3;
  assert_norm (Seq.index i3 0 == 2);
  assert_norm (Seq.index i3 1 == 1);
  count2 (Seq.index y 0) y;
  count2 (Seq.index y 1) y;
  assert (Seq.index y 0 = 1 \/ Seq.index y 0 = 2);
  assert (Seq.index y 1 = 1 \/ Seq.index y 1 = 2);
  assert (Seq.index y 0 <= Seq.index y 1);
  assert (Seq.index y 0 = 1);
  assert (Seq.index y 1 <> 1);
  assert (Seq.index y 1 = 2);
  Seq.lemma_eq_elim y o3
#pop-options
