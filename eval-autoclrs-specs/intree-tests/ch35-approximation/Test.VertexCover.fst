module Test.VertexCover
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch35.VertexCover.Impl
open CLRS.Ch35.VertexCover.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module Spec = CLRS.Ch35.VertexCover.Spec
module V = Pulse.Lib.Vec

(* Completeness lemma — proof obligation *)
#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_vertex_cover_single_edge (s_cover s_adj: Seq.seq int) : Lemma
  (requires
    Seq.length s_cover == 2 /\
    Spec.is_cover s_adj s_cover 2 2 0 /\
    (forall (i: nat). i < 2 ==> (Seq.index s_cover i == 0 \/ Seq.index s_cover i == 1)))
  (ensures Seq.index s_cover 0 == 1 /\ Seq.index s_cover 1 == 1)
= admit()
#pop-options

```pulse
fn test_vertex_cover_single_edge ()
  requires emp
  returns _: unit
  ensures emp
{
  let v = V.alloc #int 0 4sz;
  V.to_array_pts_to v;
  let adj = V.vec_to_array v;
  rewrite (A.pts_to (V.vec_to_array v) (Seq.create #int 4 0))
       as (A.pts_to adj (Seq.create #int 4 0));
  adj.(1sz) <- 1;
  adj.(2sz) <- 1;

  with s_adj. assert (A.pts_to adj s_adj);

  let cover = approx_vertex_cover #1.0R adj 2sz;

  with s_cover. assert (V.pts_to cover s_cover);

  completeness_vertex_cover_single_edge s_cover s_adj;

  V.to_array_pts_to cover;
  let cover_arr = V.vec_to_array cover;
  rewrite (A.pts_to (V.vec_to_array cover) s_cover) as (A.pts_to cover_arr s_cover);

  let c0 = cover_arr.(0sz);
  let c1 = cover_arr.(1sz);
  assert (pure (c0 == 1));
  assert (pure (c1 == 1));

  admit()
}
```
