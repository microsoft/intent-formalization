module Test.BST2
(* Second completeness example — different input *)
#lang-pulse

open Pulse.Lib.Pervasives
open CLRS.Ch12.BST.Impl
open CLRS.Ch12.BST.Spec

module GR = Pulse.Lib.GhostReference

#push-options "--fuel 8 --ifuel 4 --z3rlimit 400"
let completeness_bst_search_1 (result: bool) : Lemma
  (requires result == bst_search (bst_insert (bst_insert (bst_insert Leaf 5) 3) 7) 7)
  (ensures result == true)
= assert_norm (bst_search (bst_insert (bst_insert (bst_insert Leaf 5) 3) 7) 7 == true)
#pop-options

fn test_bst ()
  requires emp
  returns _: unit
  ensures emp
{
  let root0 : bst_ptr = None #bst_node_ptr;
  fold (bst_subtree root0 Leaf (None #bst_node_ptr));

  let ctr = GR.alloc #nat 0;

  let root1 = tree_insert root0 5 (None #bst_node_ptr) ctr;
  let root2 = tree_insert root1 3 (None #bst_node_ptr) ctr;
  let root3 = tree_insert root2 7 (None #bst_node_ptr) ctr;

  let found = tree_search root3 7 ctr;
  with cf. assert (GR.pts_to ctr cf);
  completeness_bst_search_1 found;
  assert (pure (found == true));

  admit()
}
