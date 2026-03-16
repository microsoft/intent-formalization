module Test.BFS
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch22.BFS.Impl
open CLRS.Ch22.BFS.Spec
open CLRS.Ch22.Graph.Common

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let bfs_graph_3 (sadj: Seq.seq int) : prop =
  Seq.length sadj == 9 /\
  Seq.index sadj 0 == 0 /\ Seq.index sadj 1 == 1 /\ Seq.index sadj 2 == 1 /\
  Seq.index sadj 3 == 0 /\ Seq.index sadj 4 == 0 /\ Seq.index sadj 5 == 0 /\
  Seq.index sadj 6 == 0 /\ Seq.index sadj 7 == 0 /\ Seq.index sadj 8 == 0

let no_edge_to_zero (sadj: Seq.seq int) (u: nat) : Lemma
  (requires bfs_graph_3 sadj /\ u < 3)
  (ensures ~(has_edge sadj 3 u 0))
=
  assert (~(has_edge sadj 3 u 0))

let edge_to_one_from_zero (sadj: Seq.seq int) (u: nat) : Lemma
  (requires bfs_graph_3 sadj /\ u < 3 /\ has_edge sadj 3 u 1)
  (ensures u == 0)
=
  assert (u == 0)

let edge_to_two_from_zero (sadj: Seq.seq int) (u: nat) : Lemma
  (requires bfs_graph_3 sadj /\ u < 3 /\ has_edge sadj 3 u 2)
  (ensures u == 0)
=
  assert (u == 0)

let rec reach_zero_only_at_zero (sadj: Seq.seq int) (k: nat) : Lemma
  (requires bfs_graph_3 sadj /\ reachable_in sadj 3 0 0 k)
  (ensures k == 0)
  (decreases k)
=
  if k = 0 then ()
  else
    FStar.Classical.exists_elim
      (k == 0)
      #nat
      #(fun (u: nat) -> u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 0)
      ()
      (fun (u: nat{u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 0}) ->
        no_edge_to_zero sadj u;
        assert false)

let reach_one_at_one (sadj: Seq.seq int) (k: nat) : Lemma
  (requires bfs_graph_3 sadj /\ reachable_in sadj 3 0 1 k)
  (ensures k == 1)
=
  if k = 0 then
    assert false
  else
    FStar.Classical.exists_elim
      (k == 1)
      #nat
      #(fun (u: nat) -> u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 1)
      ()
      (fun (u: nat{u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 1}) ->
        edge_to_one_from_zero sadj u;
        reach_zero_only_at_zero sadj (k - 1);
        assert (k == 1))

let reach_two_at_one (sadj: Seq.seq int) (k: nat) : Lemma
  (requires bfs_graph_3 sadj /\ reachable_in sadj 3 0 2 k)
  (ensures k == 1)
=
  if k = 0 then
    assert false
  else
    FStar.Classical.exists_elim
      (k == 1)
      #nat
      #(fun (u: nat) -> u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 2)
      ()
      (fun (u: nat{u < 3 /\ reachable_in sadj 3 0 u (k - 1) /\ has_edge sadj 3 u 2}) ->
        edge_to_two_from_zero sadj u;
        reach_zero_only_at_zero sadj (k - 1);
        assert (k == 1))

let bfs_complete (sadj: Seq.seq int) (sdist: Seq.seq int) : Lemma
  (requires
    bfs_graph_3 sadj /\
    Seq.length sdist == 3 /\
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 >= 0 /\
    Seq.index sdist 2 >= 0 /\
    reachable_in sadj 3 0 1 (Seq.index sdist 1) /\
    reachable_in sadj 3 0 2 (Seq.index sdist 2))
  (ensures
    Seq.index sdist 0 == 0 /\
    Seq.index sdist 1 == 1 /\
    Seq.index sdist 2 == 1)
=
  reach_one_at_one sadj (Seq.index sdist 1);
  reach_two_at_one sadj (Seq.index sdist 2)

```pulse
fn test_bfs ()
  requires emp
  returns _: unit
  ensures emp
{
  let adj_v = V.alloc 0 9sz;
  V.to_array_pts_to adj_v;
  let adj = V.vec_to_array adj_v;
  rewrite (A.pts_to (V.vec_to_array adj_v) (Seq.create 9 0)) as (A.pts_to adj (Seq.create 9 0));
  adj.(1sz) <- 1;
  adj.(2sz) <- 1;

  let color_v = V.alloc 0 3sz;
  V.to_array_pts_to color_v;
  let color = V.vec_to_array color_v;
  rewrite (A.pts_to (V.vec_to_array color_v) (Seq.create 3 0)) as (A.pts_to color (Seq.create 3 0));

  let dist_v = V.alloc 0 3sz;
  V.to_array_pts_to dist_v;
  let dist = V.vec_to_array dist_v;
  rewrite (A.pts_to (V.vec_to_array dist_v) (Seq.create 3 0)) as (A.pts_to dist (Seq.create 3 0));

  let pred_v = V.alloc 0 3sz;
  V.to_array_pts_to pred_v;
  let pred = V.vec_to_array pred_v;
  rewrite (A.pts_to (V.vec_to_array pred_v) (Seq.create 3 0)) as (A.pts_to pred (Seq.create 3 0));

  let queue_v = V.alloc 0sz 3sz;
  V.to_array_pts_to queue_v;
  let queue_data = V.vec_to_array queue_v;
  rewrite (A.pts_to (V.vec_to_array queue_v) (Seq.create 3 0sz)) as (A.pts_to queue_data (Seq.create 3 0sz));

  with sadj. assert (A.pts_to adj sadj);

  let ctr = GR.alloc #nat 0;
  queue_bfs adj 3sz 0sz color dist pred queue_data ctr;

  with scolor. assert (A.pts_to color scolor);
  with sdist. assert (A.pts_to dist sdist);
  with spred. assert (A.pts_to pred spred);
  with squeue. assert (A.pts_to queue_data squeue);
  with cf. assert (GR.pts_to ctr cf);

  assert (pure (reachable_in sadj 3 0 1 1));
  assert (pure (reachable_in sadj 3 0 2 1));
  assert (pure (Seq.index scolor 1 <> 0));
  assert (pure (Seq.index scolor 2 <> 0));
  assert (pure (reachable_in sadj 3 0 1 (Seq.index sdist 1)));
  assert (pure (reachable_in sadj 3 0 2 (Seq.index sdist 2)));

  bfs_complete sadj sdist;

  let d0 = dist.(0sz);
  let d1 = dist.(1sz);
  let d2 = dist.(2sz);

  assert (pure (d0 == 0));
  assert (pure (d1 == 1));
  assert (pure (d2 == 1));

  admit()
}
```