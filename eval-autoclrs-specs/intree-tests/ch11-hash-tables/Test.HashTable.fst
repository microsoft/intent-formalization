module Test.HashTable
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array
open FStar.SizeT
open FStar.Mul
open CLRS.Ch11.HashTable.Impl

module A = Pulse.Lib.Array
module GR = Pulse.Lib.GhostReference
module SZ = FStar.SizeT
module Seq = FStar.Seq
module V = Pulse.Lib.Vec

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_insert_42 (s: Seq.seq int) (ok: bool) : Lemma
  (requires Seq.length s == 5 /\
            valid_ht s 5 /\
            (if ok then key_in_table s 5 42 else s == Seq.create 5 (-1)))
  (ensures ok == true)
= admit()

let completeness_search_42 (s: Seq.seq int) (result: SZ.t) : Lemma
  (requires Seq.length s == 5 /\
            key_in_table s 5 42 /\
            SZ.v result <= 5 /\
            (SZ.v result == 5 ==> ~(key_in_table s 5 42)))
  (ensures SZ.v result < 5)
= assert (SZ.v result < 5)
#pop-options

fn test_hash_table ()
  requires emp
  returns _: unit
  ensures emp
{
  let tv = hash_table_create 5sz;
  let table = V.vec_to_array tv;
  rewrite (A.pts_to (V.vec_to_array tv) (Seq.create 5 (-1)))
       as (A.pts_to table (Seq.create 5 (-1)));

  let ctr = GR.alloc #nat 0;

  let inserted = hash_insert table 5sz 42 ctr;
  with s1 cf1.
    assert (A.pts_to table s1 ** GR.pts_to ctr cf1 **
            pure (Seq.length s1 == 5 /\
                  valid_ht s1 5 /\
                  (if inserted then key_in_table s1 5 42 else s1 == Seq.create 5 (-1))));
  completeness_insert_42 s1 inserted;
  assert (pure (inserted == true));

  let result = hash_search table 5sz 42 ctr;
  with cf2. assert (GR.pts_to ctr cf2);
  completeness_search_42 s1 result;
  assert (pure (SZ.v result < 5));

  admit()
}
