(* Second completeness example — different input *)
module Test.DFS3
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.DFS.Impl
open CLRS.Ch22.DFS.Spec

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let dfs_complete (scolor sd sf: Seq.seq int) : Lemma
  (requires
    Seq.length scolor == 2 /\
    Seq.length sd == 2 /\
    Seq.length sf == 2 /\
    (forall (u: nat). u < 2 ==> Seq.index scolor u == 2) /\
    (forall (u: nat). u < 2 ==> Seq.index sd u < Seq.index sf u))
  (ensures
    Seq.index scolor 0 == 2 /\
    Seq.index scolor 1 == 2 /\
    Seq.index sd 0 < Seq.index sf 0 /\
    Seq.index sd 1 < Seq.index sf 1)
=
  assert (Seq.index scolor 0 == 2);
  assert (Seq.index scolor 1 == 2);
  assert (Seq.index sd 0 < Seq.index sf 0);
  assert (Seq.index sd 1 < Seq.index sf 1)

```pulse
fn test_dfs3 ()
  requires emp
  returns _: unit
  ensures emp
{
  let adj_v = V.alloc 0 4sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 4 0)) as (A.pts_to adj (Seq.create 4 0));
  adj.(1sz) <- 1;

  let color_v = V.alloc 0 2sz;
  V.to_array_pts_to color_v;
  let color = V.vec_to_array color_v;
  rewrite (A.pts_to (V.vec_to_array color_v) (Seq.create 2 0)) as (A.pts_to color (Seq.create 2 0));

  let d_v = V.alloc 0 2sz;
  V.to_array_pts_to d_v;
  let d = V.vec_to_array d_v;
  rewrite (A.pts_to (V.vec_to_array d_v) (Seq.create 2 0)) as (A.pts_to d (Seq.create 2 0));

  let f_v = V.alloc 0 2sz;
  V.to_array_pts_to f_v;
  let f = V.vec_to_array f_v;
  rewrite (A.pts_to (V.vec_to_array f_v) (Seq.create 2 0)) as (A.pts_to f (Seq.create 2 0));

  let pred_v = V.alloc 0 2sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 2 0)) as (A.pts_to pred (Seq.create 2 0));

  let stack_v = V.alloc 0sz 2sz;
  V.to_array_pts_to stack_v;
  let stack_data = V.vec_to_array stack_v;
  rewrite (A.pts_to (V.vec_to_array stack_v) (Seq.create 2 0sz)) as (A.pts_to stack_data (Seq.create 2 0sz));

  let scan_v = V.alloc 0sz 2sz;
  V.to_array_pts_to scan_v;
  let scan_idx = V.vec_to_array scan_v;
  rewrite (A.pts_to (V.vec_to_array scan_v) (Seq.create 2 0sz)) as (A.pts_to scan_idx (Seq.create 2 0sz));

  let ctr = GR.alloc #nat 0;
  stack_dfs adj 2sz color d f pred stack_data scan_idx ctr;

  with scolor. assert (A.pts_to color scolor);
  with sd. assert (A.pts_to d sd);
  with sf. assert (A.pts_to f sf);
  with spred. assert (A.pts_to pred spred);
  with sstack. assert (A.pts_to stack_data sstack);
  with sscan. assert (A.pts_to scan_idx sscan);
  with cf. assert (GR.pts_to ctr cf);

  dfs_complete scolor sd sf;

  let c0 = color.(0sz);
  let c1 = color.(1sz);
  let d0 = d.(0sz);
  let d1 = d.(1sz);
  let f0 = f.(0sz);
  let f1 = f.(1sz);

  assert (pure (c0 == 2));
  assert (pure (c1 == 2));
  assert (pure (d0 < f0));
  assert (pure (d1 < f1));

  admit()
}
```
