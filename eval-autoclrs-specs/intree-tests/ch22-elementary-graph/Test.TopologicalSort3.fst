(* Second completeness example — different input *)
module Test.TopologicalSort3
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

   Graph: 4 vertices, edges: 0->1, 1->2, 2->3 (simple DAG)
   Adjacency matrix (flat, row-major):
   [0;1;0;0; 0;0;1;0; 0;0;0;1; 0;0;0;0]
   Expected output: [0; 1; 2; 3] (the unique valid topological order)
   ================================================================ *)

(* --- Acyclicity lemma: prove the test graph has no cycle --- *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let no_cycle_4 (adj: Seq.seq int) : Lemma
  (requires
    Seq.length adj == 16 /\
    Seq.index adj 0 == 0 /\ Seq.index adj 1 == 1 /\ Seq.index adj 2 == 0 /\ Seq.index adj 3 == 0 /\
    Seq.index adj 4 == 0 /\ Seq.index adj 5 == 0 /\ Seq.index adj 6 == 1 /\ Seq.index adj 7 == 0 /\
    Seq.index adj 8 == 0 /\ Seq.index adj 9 == 0 /\ Seq.index adj 10 == 0 /\ Seq.index adj 11 == 1 /\
    Seq.index adj 12 == 0 /\ Seq.index adj 13 == 0 /\ Seq.index adj 14 == 0 /\ Seq.index adj 15 == 0)
  (ensures ~(has_cycle adj 4))
=
  assert (has_edge 4 adj 0 0 == false);
  assert (has_edge 4 adj 0 1 == true);
  assert (has_edge 4 adj 0 2 == false);
  assert (has_edge 4 adj 0 3 == false);
  assert (has_edge 4 adj 1 0 == false);
  assert (has_edge 4 adj 1 1 == false);
  assert (has_edge 4 adj 1 2 == true);
  assert (has_edge 4 adj 1 3 == false);
  assert (has_edge 4 adj 2 0 == false);
  assert (has_edge 4 adj 2 1 == false);
  assert (has_edge 4 adj 2 2 == false);
  assert (has_edge 4 adj 2 3 == true);
  assert (has_edge 4 adj 3 0 == false);
  assert (has_edge 4 adj 3 1 == false);
  assert (has_edge 4 adj 3 2 == false);
  assert (has_edge 4 adj 3 3 == false)
#pop-options

(* --- Completeness lemma: topological order is uniquely [0;1;2;3] --- *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_topo_4 (sout: Seq.seq int) (adj: Seq.seq int) : Lemma
  (requires
    Seq.length adj == 16 /\
    Seq.index adj 0 == 0 /\ Seq.index adj 1 == 1 /\ Seq.index adj 2 == 0 /\ Seq.index adj 3 == 0 /\
    Seq.index adj 4 == 0 /\ Seq.index adj 5 == 0 /\ Seq.index adj 6 == 1 /\ Seq.index adj 7 == 0 /\
    Seq.index adj 8 == 0 /\ Seq.index adj 9 == 0 /\ Seq.index adj 10 == 0 /\ Seq.index adj 11 == 1 /\
    Seq.index adj 12 == 0 /\ Seq.index adj 13 == 0 /\ Seq.index adj 14 == 0 /\ Seq.index adj 15 == 0 /\
    Seq.length sout == 4 /\
    (forall (i:nat). i < 4 ==> Seq.index sout i >= 0) /\
    (forall (i:nat). i < 4 ==> Seq.index sout i < 4) /\
    all_distinct (seq_int_to_nat sout) /\
    is_topological_order adj 4 (seq_int_to_nat sout))
  (ensures Seq.index sout 0 == 0 /\ Seq.index sout 1 == 1 /\ Seq.index sout 2 == 2 /\ Seq.index sout 3 == 3)
=
  assert (has_edge 4 adj 0 1 == true);
  assert (has_edge 4 adj 1 2 == true);
  assert (has_edge 4 adj 2 3 == true)
#pop-options

```pulse
(* Completeness: y = topological_sort(x); assert(y == expected) *)
fn test_topological_sort3 ()
  requires emp
  returns _: unit
  ensures emp
{
  // Input: 4x4 adjacency matrix for graph 0->1->2->3
  let v = V.alloc 0 16sz;
  V.to_array_pts_to v;
  let adj = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create 16 0))
       as (A.pts_to adj (Seq.create 16 0));

  // Set edges: 0->1 (index 1), 1->2 (index 6), 2->3 (index 11)
  adj.(1sz) <- 1;
  adj.(6sz) <- 1;
  adj.(11sz) <- 1;

  // Bind input ghost
  with s0. assert (A.pts_to adj s0);

  // Prove acyclicity (required precondition)
  no_cycle_4 s0;

  // Allocate ghost complexity counter
  let ctr = GR.alloc #nat 0;

  // y = topological_sort(x)
  let output = topological_sort adj 4sz ctr;

  // Extract postcondition existentials
  with sout. assert (V.pts_to output sout);
  with cf. assert (GR.pts_to ctr cf);

  // Apply completeness lemma: output must be [0; 1; 2; 3]
  completeness_topo_4 sout s0;

  // Convert output vec to array for reading
  V.to_array_pts_to output;
  let oarr = V.vec_to_array output;
  rewrite (A.pts_to (V.vec_to_array output) sout) as (A.pts_to oarr sout);

  // Read and verify output values
  let v0 = oarr.(0sz);  // output[0]
  let v1 = oarr.(1sz);  // output[1]
  let v2 = oarr.(2sz);  // output[2]
  let v3 = oarr.(3sz);  // output[3]

  assert (pure (v0 == 0));
  assert (pure (v1 == 1));
  assert (pure (v2 == 2));
  assert (pure (v3 == 3));

  admit()
}
```
