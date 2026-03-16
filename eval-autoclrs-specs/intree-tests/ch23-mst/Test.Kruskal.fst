module Test.Kruskal
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open Pulse.Lib.Reference
open FStar.SizeT
open FStar.Mul
open CLRS.Ch23.Kruskal.Impl
open CLRS.Ch23.MST.Spec
open CLRS.Ch23.Kruskal.Spec

module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let kruskal_complete (sadj seu sev: Seq.seq int) (ec: SZ.t) : Lemma
  (requires
    Seq.length sadj == 4 /\
    Seq.index sadj 0 == 0 /\ Seq.index sadj 1 == 5 /\
    Seq.index sadj 2 == 5 /\ Seq.index sadj 3 == 0 /\
    Seq.length seu == 2 /\
    Seq.length sev == 2 /\
    result_is_forest_adj sadj seu sev 2 (SZ.v ec))
  (ensures
    SZ.v ec == 1 /\
    Seq.index seu 0 == 0 /\
    Seq.index sev 0 == 1)
=
  admit()

```pulse
fn test_kruskal ()
  requires emp
  returns _: unit
  ensures emp
{
  let adj_v = V.alloc 0 4sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 4 0)) as (A.pts_to adj (Seq.create 4 0));
  adj.(1sz) <- 5;
  adj.(2sz) <- 5;

  let edge_u_v = V.alloc 0 2sz;
  V.to_array_pts_to edge_u_v;
  let edge_u = V.vec_to_array edge_u_v;
  rewrite (A.pts_to (V.vec_to_array edge_u_v) (Seq.create 2 0)) as (A.pts_to edge_u (Seq.create 2 0));

  let edge_v_v = V.alloc 0 2sz;
  V.to_array_pts_to edge_v_v;
  let edge_v = V.vec_to_array edge_v_v;
  rewrite (A.pts_to (V.vec_to_array edge_v_v) (Seq.create 2 0)) as (A.pts_to edge_v (Seq.create 2 0));

  with sadj. assert (A.pts_to adj sadj);
  let edge_count = R.alloc 0sz;

  kruskal adj edge_u edge_v edge_count 2sz;

  with seu. assert (A.pts_to edge_u seu);
  assert (pure (Seq.length seu == 2));
  with sev. assert (A.pts_to edge_v sev);
  assert (pure (Seq.length sev == 2));
  with ec. assert (R.pts_to edge_count ec);
  assert (pure (result_is_forest_adj sadj seu sev 2 (SZ.v ec)));

  kruskal_complete sadj seu sev ec;

  let count = R.(!edge_count);
  let u0 = edge_u.(0sz);
  let v0 = edge_v.(0sz);

  assert (pure (count == 1sz));
  assert (pure (u0 == 0));
  assert (pure (v0 == 1));

  admit()
}
```