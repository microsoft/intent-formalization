# Completeness Test Patterns for AutoCLRS

Reference patterns for writing completeness tests that call Pulse implementations.
Each test follows: `test(x) { y = algorithm(x); assert(y == expected) }`.

**Key principle:** Only prove the completeness assertion (`assert(y == expected)`).
Use `admit()` after assertions to skip resource cleanup — it's irrelevant to completeness.

## Incremental Verification

Use `verify-test.sh` (in WSL build tree) to verify just one test file (~3-5s):

```bash
# First time: build chapter deps
cd /root/autoclrs-build/autoclrs/<chapter> && make verify

# Then iterate on test file only:
/root/autoclrs-build/verify-test.sh <chapter-dir> <TestFile.fst>
```

## Pattern 1: Sorting (Array In-Place) — e.g. Quicksort

**Impl:** `fn quicksort (arr: A.array int) (len: SZ.t)`
- Postcondition: `sorted s /\ permutation s0 s`
- Needs BoundedIntegers bridge for `CLRS.Common.SortSpec.sorted`

```fstar
(* Bridge BoundedIntegers <= to Prims <= for Z3 *)
let completeness (s: Seq.seq int) : Lemma
  (requires SS.sorted s /\ SP.permutation int input s)
  (ensures Seq.index s 0 == expected0 /\ ...) =
  assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  (* then count-based uniqueness proof *)

fn test () requires emp ensures emp {
  (* ... alloc, write input, call quicksort ... *)
  with s. assert (A.pts_to arr s);
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  completeness s;
  let v0 = arr.(0sz); ...
  assert (pure (v0 == expected0));
  admit()  // skip cleanup
}
```

## Pattern 2: Graph (Vec Output + Ghost Ref) — e.g. TopologicalSort

**Impl:** `fn topological_sort (adj: A.array int) (n: SZ.t) (ctr: GR.ref nat)`
- Precondition: `~(has_cycle sadj n)` — prove via edge enumeration
- Output: `V.vec int` — convert to array to read

```fstar
(* Acyclicity: enumerate all edges *)
let no_cycle (adj: Seq.seq int) : Lemma (...) (ensures ~(has_cycle adj n)) =
  assert (has_edge n adj 0 0 == false); ...

fn test () requires emp ensures emp {
  (* ... alloc adj, write edges ... *)
  with s0. assert (A.pts_to adj s0);
  no_cycle s0;
  let ctr = GR.alloc #nat 0;
  let output = topological_sort adj 3sz ctr;
  with sout. assert (V.pts_to output sout);
  with cf. assert (GR.pts_to ctr cf);
  completeness sout s0;
  V.to_array_pts_to output;
  let oarr = V.vec_to_array output;
  rewrite ...;
  let v0 = oarr.(0sz); ...
  assert (pure (v0 == expected));
  admit()
}
```

## Pattern 3: Pure Spec (No Pulse Impl)

```fstar
let test (y: int) : Lemma (requires y == gcd 12 8) (ensures y == 4) =
  normalize_term_spec (gcd 12 8)
```

## Chapters with ../common include
ch02, ch07, ch09, ch10, ch15, ch21, ch22, ch23, ch31, ch32
These use `CLRS.Common.SortSpec` with BoundedIntegers operators.

