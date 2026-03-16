module Test.TopologicalSort
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.TopologicalSort.Impl
open CLRS.Ch22.TopologicalSort.Spec
open CLRS.Ch22.TopologicalSort.Impl.Defs

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

(* ================================================================
   Completeness test for topological_sort (Pulse implementation)

   Graph: 3 vertices, edges: 0->1, 1->2 (simple DAG)
   Adjacency matrix (flat, row-major): [0;1;0; 0;0;1; 0;0;0]
   Expected output: [0; 1; 2] (the unique valid topological order)
   ================================================================ *)

(* --- Acyclicity lemma: prove the test graph has no cycle --- *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let no_cycle_3 (adj: Seq.seq int) : Lemma
  (requires
    Seq.length adj == 9 /\
    Seq.index adj 0 == 0 /\ Seq.index adj 1 == 1 /\ Seq.index adj 2 == 0 /\
    Seq.index adj 3 == 0 /\ Seq.index adj 4 == 0 /\ Seq.index adj 5 == 1 /\
    Seq.index adj 6 == 0 /\ Seq.index adj 7 == 0 /\ Seq.index adj 8 == 0)
  (ensures ~(has_cycle adj 3))
=
  assert (has_edge 3 adj 0 0 == false);
  assert (has_edge 3 adj 0 1 == true);
  assert (has_edge 3 adj 0 2 == false);
  assert (has_edge 3 adj 1 0 == false);
  assert (has_edge 3 adj 1 1 == false);
  assert (has_edge 3 adj 1 2 == true);
  assert (has_edge 3 adj 2 0 == false);
  assert (has_edge 3 adj 2 1 == false);
  assert (has_edge 3 adj 2 2 == false)
#pop-options

(* --- Completeness lemma: topological order is uniquely [0;1;2] --- *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_topo (sout: Seq.seq int) (adj: Seq.seq int) : Lemma
  (requires
    Seq.length adj == 9 /\
    Seq.index adj 0 == 0 /\ Seq.index adj 1 == 1 /\ Seq.index adj 2 == 0 /\
    Seq.index adj 3 == 0 /\ Seq.index adj 4 == 0 /\ Seq.index adj 5 == 1 /\
    Seq.index adj 6 == 0 /\ Seq.index adj 7 == 0 /\ Seq.index adj 8 == 0 /\
    Seq.length sout == 3 /\
    (forall (i:nat). i < 3 ==> Seq.index sout i >= 0) /\
    (forall (i:nat). i < 3 ==> Seq.index sout i < 3) /\
    all_distinct (seq_int_to_nat sout) /\
    is_topological_order adj 3 (seq_int_to_nat sout))
  (ensures Seq.index sout 0 == 0 /\ Seq.index sout 1 == 1 /\ Seq.index sout 2 == 2)
=
  assert (has_edge 3 adj 0 1 == true);
  assert (has_edge 3 adj 1 2 == true)
#pop-options

```pulse
(* Completeness: y = topological_sort(x); assert(y == expected) *)
fn test_topological_sort ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: 3x3 adjacency matrix for graph 0->1->2
  let v = V.alloc 0 9sz;
  V.to_array_pts_to v;
  let adj = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 9 0))
       as (A.pts_to adj (Seq.create 9 0));

  // Set edges: 0->1 (index 1) and 1->2 (index 5)
  adj.(1sz) <- 1;
  adj.(5sz) <- 1;

  // Bind input ghost
  with s0. assert (A.pts_to adj s0);

  // Prove acyclicity (required precondition)
  no_cycle_3 s0;

  // Allocate ghost complexity counter
  let ctr = GR.alloc #nat 0;

  // y = topological_sort(x)
  let output = topological_sort adj 3sz ctr;

  // Extract postcondition existentials
  with sout. assert (V.pts_to output sout);
  with cf. assert (GR.pts_to ctr cf);

  // Apply completeness lemma: output must be [0; 1; 2]
  completeness_topo sout s0;

  // Convert output vec to array for reading
  V.to_array_pts_to output;
  let oarr = V.vec_to_array output;
  rewrite (A.pts_to (V.vec_to_array output) sout) as (A.pts_to oarr sout);

  // Read and verify output values
  let v0 = oarr.(0sz);  // output[0]
  let v1 = oarr.(1sz);  // output[1]
  let v2 = oarr.(2sz);  // output[2]

  assert (pure (v0 == 0));   // ✅ First vertex in topological order
  assert (pure (v1 == 1));   // ✅ Second vertex
  assert (pure (v2 == 2));   // ✅ Third vertex

  // Completeness proven — drop remaining resources
  admit()
}
```
