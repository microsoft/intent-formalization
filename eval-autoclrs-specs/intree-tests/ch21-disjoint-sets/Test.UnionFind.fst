module Test.UnionFind
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open CLRS.Ch21.UnionFind.Impl

module A = Pulse.Lib.Array
module Seq = FStar.Seq
module Spec = CLRS.Ch21.UnionFind.Spec
module SZ = FStar.SizeT
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_union_find_same_root
  (sp sp': Seq.seq SZ.t)
  (sr: Seq.seq SZ.t)
  (r0 r1: SZ.t)
  : Lemma
    (requires Spec.uf_inv (to_uf sp sr 3) /\
              Spec.uf_inv (to_uf sp' sr 3) /\
              Spec.pure_find (to_uf sp sr 3) 0 == Spec.pure_find (to_uf sp sr 3) 1 /\
              (forall (z: nat). z < 3 ==> Spec.pure_find (to_uf sp' sr 3) z == Spec.pure_find (to_uf sp sr 3) z) /\
              SZ.v r0 == Spec.pure_find (to_uf sp sr 3) 0 /\
              SZ.v r1 == Spec.pure_find (to_uf sp' sr 3) 1)
    (ensures r0 == r1)
= assert (Spec.pure_find (to_uf sp' sr 3) 1 == Spec.pure_find (to_uf sp sr 3) 1);
  assert (SZ.v r0 == Spec.pure_find (to_uf sp sr 3) 1);
  assert (SZ.v r0 == SZ.v r1);
  assert (r0 == r1)
#pop-options

fn test_union_find ()
  requires emp
  returns _: unit
  ensures emp
{
  let pv = V.alloc 0sz 3sz;
  V.to_array_pts_to pv;
  let parent = V.vec_to_array pv;
  rewrite (A.pts_to (V.vec_to_array pv) (Seq.create 3 0sz))
       as (A.pts_to parent (Seq.create 3 0sz));

  let rv = V.alloc 0sz 3sz;
  V.to_array_pts_to rv;
  let rank = V.vec_to_array rv;
  rewrite (A.pts_to (V.vec_to_array rv) (Seq.create 3 0sz))
       as (A.pts_to rank (Seq.create 3 0sz));

  make_set parent rank 3sz;
  union parent rank 0sz 1sz 3sz;

  with sp sr.
    assert (A.pts_to parent sp ** A.pts_to rank sr **
            pure (Spec.uf_inv (to_uf sp sr 3) /\
                  Spec.pure_find (to_uf sp sr 3) 0 == Spec.pure_find (to_uf sp sr 3) 1));

  let r0 = find_set parent 0sz 3sz #sp #sr;
  with sp'.
    assert (A.pts_to parent sp' **
            pure (Spec.uf_inv (to_uf sp' sr 3) /\
                  (forall (z: nat). z < 3 ==> Spec.pure_find (to_uf sp' sr 3) z == Spec.pure_find (to_uf sp sr 3) z) /\
                  SZ.v r0 == Spec.pure_find (to_uf sp sr 3) 0));

  let r1 = find_set parent 1sz 3sz #sp' #sr;
  with sp''.
    assert (A.pts_to parent sp'' **
            pure (SZ.v r1 == Spec.pure_find (to_uf sp' sr 3) 1));

  completeness_union_find_same_root sp sp' sr r0 r1;
  assert (pure (r0 == r1));

  admit()
}
