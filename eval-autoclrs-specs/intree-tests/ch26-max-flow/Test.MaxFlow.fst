module Test.MaxFlow
#lang-pulse

friend CLRS.Ch26.MaxFlow.Impl

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch26.MaxFlow.Impl
open CLRS.Ch26.MaxFlow.Spec

module A = Pulse.Lib.Array
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

let max_flow_caps_ok (cap_seq: Seq.seq int) : Lemma
  (requires
    Seq.length cap_seq == 4 /\
    Seq.index cap_seq 0 == 0 /\ Seq.index cap_seq 1 == 10 /\
    Seq.index cap_seq 2 == 0 /\ Seq.index cap_seq 3 == 0)
  (ensures valid_caps cap_seq 2)
=
  assert_norm (valid_caps cap_seq 2)

let max_flow_complete (cap_seq flow_seq: Seq.seq int) : Lemma
  (requires
    Seq.length cap_seq == 4 /\
    Seq.index cap_seq 0 == 0 /\ Seq.index cap_seq 1 == 10 /\
    Seq.index cap_seq 2 == 0 /\ Seq.index cap_seq 3 == 0 /\
    Seq.length flow_seq == 4 /\
    imp_valid_flow flow_seq cap_seq 2 0 1 /\
    no_augmenting_path #2 cap_seq flow_seq 0 1)
  (ensures
    Seq.index flow_seq 0 == 0 /\
    Seq.index flow_seq 1 == 10 /\
    Seq.index flow_seq 2 == 0 /\
    Seq.index flow_seq 3 == 0)
=
  imp_valid_flow_implies_valid_flow flow_seq cap_seq 2 0 1;
  assert (valid_flow #2 flow_seq cap_seq 0 1);
  assert (0 <= get flow_seq 2 0 0 /\ get flow_seq 2 0 0 <= get cap_seq 2 0 0);
  assert (0 <= get flow_seq 2 1 0 /\ get flow_seq 2 1 0 <= get cap_seq 2 1 0);
  assert (0 <= get flow_seq 2 1 1 /\ get flow_seq 2 1 1 <= get cap_seq 2 1 1);
  assert (0 <= get flow_seq 2 0 1 /\ get flow_seq 2 0 1 <= get cap_seq 2 0 1);
  assert (Seq.index flow_seq 0 == 0)
    by (FStar.Tactics.norm [delta_only [`%get]];
        FStar.Tactics.smt ());
  assert (Seq.index flow_seq 2 == 0)
    by (FStar.Tactics.norm [delta_only [`%get]];
        FStar.Tactics.smt ());
  assert (Seq.index flow_seq 3 == 0)
    by (FStar.Tactics.norm [delta_only [`%get]];
        FStar.Tactics.smt ());
  assert (0 <= Seq.index flow_seq 1 /\ Seq.index flow_seq 1 <= 10)
    by (FStar.Tactics.norm [delta_only [`%get]];
        FStar.Tactics.smt ());
  if Seq.index flow_seq 1 = 10 then ()
  else begin
    assert (Seq.index flow_seq 1 < 10);
    assert (bottleneck cap_seq flow_seq 2 [0; 1] <= 0)
      by (FStar.Tactics.norm [delta_only [`%no_augmenting_path]];
          FStar.Tactics.smt ());
    assert (bottleneck cap_seq flow_seq 2 [0; 1] > 0)
      by (FStar.Tactics.norm [delta_only [`%bottleneck; `%bottleneck_aux; `%residual_capacity; `%residual_capacity_backward; `%get]];
          FStar.Tactics.smt ());
    assert false
  end;
  assert (Seq.index flow_seq 1 == 10)

```pulse
fn test_max_flow ()
  requires emp
  returns _: unit
  ensures emp
{
  let cap_v = V.alloc 0 4sz;
  V.to_array_pts_to cap_v;
  let capacity = V.vec_to_array cap_v;
  rewrite (A.pts_to (V.vec_to_array cap_v) (Seq.create 4 0)) as (A.pts_to capacity (Seq.create 4 0));
  capacity.(1sz) <- 10;

  with cap_seq. assert (A.pts_to capacity cap_seq);
  max_flow_caps_ok cap_seq;

  let flow_v = V.alloc 0 4sz;
  V.to_array_pts_to flow_v;
  let flow = V.vec_to_array flow_v;
  rewrite (A.pts_to (V.vec_to_array flow_v) (Seq.create 4 0)) as (A.pts_to flow (Seq.create 4 0));

  max_flow capacity flow 2sz 0sz 1sz;

  with flow_seq.
    assert (A.pts_to flow flow_seq **
            pure (Seq.length flow_seq == 4 /\
                  imp_valid_flow flow_seq cap_seq 2 0 1 /\
                  no_augmenting_path #2 cap_seq flow_seq 0 1));
  max_flow_complete cap_seq flow_seq;

  let f00 = flow.(0sz);
  let f01 = flow.(1sz);
  let f10 = flow.(2sz);
  let f11 = flow.(3sz);

  assert (pure (f00 == 0));
  assert (pure (f01 == 10));
  assert (pure (f10 == 0));
  assert (pure (f11 == 0));

  admit()
}
```