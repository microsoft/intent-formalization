# Intent Formalization for AutoCLRS Algorithms

Symbolic testing of F* specifications from the
[AutoCLRS](https://github.com/FStarLang/AutoCLRS) repository — verified
implementations of 52 algorithms from *Introduction to Algorithms* (CLRS).

See the [Intent Formalization blog](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/) for an overview of the research direction.

Uses the **soundness and completeness testing** approach from:

> **Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages**
> *Shuvendu K. Lahiri*, FMCAD 2024.
> [https://arxiv.org/abs/2406.09757](https://arxiv.org/abs/2406.09757)
>
> Specifically, the **Appendix B** method for completeness checking.

## Method

Given a formal specification φ(x, y) and concrete test cases {(i₁, o₁), …, (iₙ, oₙ)}:

| Property | Question | F* Encoding |
|----------|----------|-------------|
| **Soundness** | Does φ hold on known-good I/O? | `Lemma (φ(input, expected))` |
| **Completeness** ([Appendix B](https://arxiv.org/abs/2406.09757)) | Does φ uniquely determine the output? | `Lemma (requires φ(input, y)) (ensures y == expected)` |

A specification that is **sound but incomplete** accepts the correct output but also
admits wrong outputs (e.g., "sorted" without "permutation" for sorting).

### In-Tree F* Tests

Test files are placed **directly in AutoCLRS chapter directories** and verified using
the same `make verify` build system. This ensures:

- **Faithful spec evaluation** — tests import and call the exact AutoCLRS specifications
- **No override/copy mechanisms** — the build system handles all dependencies
- **`friend` declarations** for modules with abstract `.fsti` interfaces (e.g., `ShortestPath.Inf`)

## AutoCLRS Snapshot

Specifications evaluated against AutoCLRS at commit
[`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d)
(March 2026). See the [AutoCLRS blog post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
for details on the verified CLRS algorithms.

## Evaluation Results — 44/47 Algorithms Verified ✅

**326 total assertions**: 186 soundness + 140 completeness across 22 chapters.

| # | Algorithm | Ch | Test File | Sound | Complete | Notes |
|---|-----------|-----|-----------|-------|----------|-------|
| 1 | InsertionSort | ch02 | [Test.InsertionSort.fst](intree-tests/ch02-getting-started/Test.InsertionSort.fst) | 3 | 3 | sorted + permutation (Pulse) |
| 2 | MergeSort | ch02 | [Test.MergeSort.fst](intree-tests/ch02-getting-started/Test.MergeSort.fst) | 4 | 2 | seq_merge (Pulse) |
| 3 | BinarySearch | ch04 | [Test.BinarySearch.fst](intree-tests/ch04-divide-conquer/Test.BinarySearch.fst) | 3 | 2 | imperative (Pulse) |
| 4 | MaxSubarray | ch04 | [Test.MaxSubarray.fst](intree-tests/ch04-divide-conquer/Test.MaxSubarray.fst) | ✅ 4 | ✅ 4 | max contiguous sum |
| 5 | MatrixMultiply | ch04 | [Test.MatrixMultiply.fst](intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst) | ✅ 4 | ✅ 2 | dot product spec |
| 6 | Heap | ch06 | [Test.Heap.fst](intree-tests/ch06-heapsort/Test.Heap.fst) | ✅ 7 | ✅ 4 | parent/left/right/swap |
| 7 | Quicksort | ch07 | [Test.Quicksort.fst](intree-tests/ch07-quicksort/Test.Quicksort.fst) | ✅ 5 | ✅ 4 | partition + sort |
| 8 | BucketSort | ch08 | [Test.BucketSort.fst](intree-tests/ch08-linear-sorting/Test.BucketSort.fst) | ✅ 5 | ✅ 3 | bucket distribution |
| 9 | CountingSort | ch08 | [Test.CountingSort.fst](intree-tests/ch08-linear-sorting/Test.CountingSort.fst) | ✅ 4 | — | prop predicates (no output) |
| 10 | RadixSort | ch08 | [Test.RadixSort.fst](intree-tests/ch08-linear-sorting/Test.RadixSort.fst) | ✅ 3 | ✅ 3 | digit-wise sort |
| 11 | MinMax | ch09 | [Test.MinMax.fst](intree-tests/ch09-order-statistics/Test.MinMax.fst) | ✅ 4 | ✅ 3 | complexity bounds (tight) |
| 12 | SimultaneousMinMax | ch09 | [Test.SimultaneousMinMax.fst](intree-tests/ch09-order-statistics/Test.SimultaneousMinMax.fst) | ✅ 3 | ✅ 1 | tight bound only |
| 13 | PartialSelectionSort | ch09 | [Test.PartialSelectionSort.fst](intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst) | ✅ 4 | ✅ 3 | selection sort |
| 14 | Quickselect | ch09 | [Test.Quickselect.fst](intree-tests/ch09-order-statistics/Test.Quickselect.fst) | ✅ 3 | — | prop predicates (no output) |
| 15 | Stack | ch10 | [Test.Stack.fst](intree-tests/ch10-elementary-ds/Test.Stack.fst) | ✅ 6 | ✅ 4 | push/pop/empty |
| 16 | Queue | ch10 | [Test.Queue.fst](intree-tests/ch10-elementary-ds/Test.Queue.fst) | ✅ 6 | ✅ 5 | enqueue/dequeue FIFO |
| 17 | SLL | ch10 | [Test.SLL.fst](intree-tests/ch10-elementary-ds/Test.SLL.fst) | ✅ 4 | ✅ 4 | insert/search/length |
| 18 | DLL | ch10 | [Test.DLL.fst](intree-tests/ch10-elementary-ds/Test.DLL.fst) | ✅ 4 | ✅ 4 | insert/delete |
| 19 | HashTable | ch11 | [Test.HashTable.fst](intree-tests/ch11-hash-tables/Test.HashTable.fst) | ✅ 5 | ✅ 3 | hash chain insert/search |
| 20 | BST | ch12 | [Test.BST.fst](intree-tests/ch12-bst/Test.BST.fst) | ✅ 7 | ✅ 6 | search/insert/delete/inorder |
| 21 | BSTArray | ch12 | [Test.BSTArray.fst](intree-tests/ch12-bst/Test.BSTArray.fst) | ✅ 2 | ✅ 2 | pure_search (base cases) |
| 22 | RBTree | ch13 | [Test.RBTree.fst](intree-tests/ch13-rbtree/Test.RBTree.fst) | ✅ 8 | ✅ 6 | insert/search/color |
| 23 | LCS | ch15 | [Test.LCS.fst](intree-tests/ch15-dynamic-programming/Test.LCS.fst) | ✅ 4 | ✅ 4 | longest common subseq |
| 24 | MatrixChain | ch15 | [Test.MatrixChain.fst](intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst) | ✅ 1 | ✅ 1 | mc_inner_k (norm-limited) |
| 25 | RodCutting | ch15 | [Test.RodCutting.fst](intree-tests/ch15-dynamic-programming/Test.RodCutting.fst) | ✅ 4 | ✅ 4 | optimal revenue DP |
| 26 | ActivitySelection | ch16 | [Test.ActivitySelection.fst](intree-tests/ch16-greedy/Test.ActivitySelection.fst) | ✅ 3 | — | prop predicates (not unique) |
| 27 | Huffman | ch16 | [Test.Huffman.fst](intree-tests/ch16-greedy/Test.Huffman.fst) | ✅ 6 | ✅ 5 | encoding tree build |
| 28 | UnionFind | ch21 | [Test.UnionFind.fst](intree-tests/ch21-disjoint-sets/Test.UnionFind.fst) | ✅ 3 | ✅ 2 | find (norm-limited) |
| 29 | BFS | ch22 | [Test.BFS.fst](intree-tests/ch22-elementary-graph/Test.BFS.fst) | ✅ 6 | ✅ 5 | init state + enqueue |
| 30 | DFS | ch22 | [Test.DFS.fst](intree-tests/ch22-elementary-graph/Test.DFS.fst) | ✅ 6 | ✅ 3 | discover/color/time |
| 31 | TopologicalSort | ch22 | [Test.TopologicalSort.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort.fst) | ✅ 4 | ✅ 4 | has_edge predicate |
| 32 | Kruskal | ch23 | [Test.Kruskal.fst](intree-tests/ch23-mst/Test.Kruskal.fst) | ✅ 3 | ✅ 3 | MST edge spec |
| 33 | Prim | ch23 | [Test.Prim.fst](intree-tests/ch23-mst/Test.Prim.fst) | ✅ 1 | ✅ 1 | friend for Prim.Spec |
| 34 | BellmanFord | ch24 | [Test.BellmanFord.fst](intree-tests/ch24-sssp/Test.BellmanFord.fst) | ✅ 3 | ✅ 2 | friend for ShortestPath.Inf |
| 35 | Dijkstra | ch24 | [Test.Dijkstra.fst](intree-tests/ch24-sssp/Test.Dijkstra.fst) | ✅ 3 | ✅ 2 | friend for ShortestPath.Inf |
| 36 | FloydWarshall | ch25 | [Test.FloydWarshall.fst](intree-tests/ch25-apsp/Test.FloydWarshall.fst) | ✅ 2 | ✅ 2 | APSP (z3rlimit 100) |
| 37 | MaxFlow | ch26 | [Test.MaxFlow.fst](intree-tests/ch26-max-flow/Test.MaxFlow.fst) | ✅ 4 | ✅ 3 | residual capacity |
| 38 | GCD | ch31 | [Test.GCD.fst](intree-tests/ch31-number-theory/Test.GCD.fst) | ✅ 3 | ✅ 3 | Euclidean GCD |
| 39 | ModExp | ch31 | [Test.ModExp.fst](intree-tests/ch31-number-theory/Test.ModExp.fst) | ✅ 3 | ✅ 3 | modular exponentiation |
| 40 | ExtendedGCD | ch31 | [Test.ExtendedGCD.fst](intree-tests/ch31-number-theory/Test.ExtendedGCD.fst) | ✅ 3 | ✅ 3 | Bézout coefficients |
| 41 | NaiveStringMatch | ch32 | [Test.NaiveStringMatch.fst](intree-tests/ch32-string-matching/Test.NaiveStringMatch.fst) | ✅ 4 | ✅ 4 | brute-force matching |
| 42 | RabinKarp | ch32 | [Test.RabinKarp.fst](intree-tests/ch32-string-matching/Test.RabinKarp.fst) | ✅ 6 | ✅ 6 | hash-based matching |
| 43 | KMP | ch32 | [Test.KMP.fst](intree-tests/ch32-string-matching/Test.KMP.fst) | ✅ 3 | — | prop predicates (not unique) |
| 44 | Segments | ch33 | [Test.Segments.fst](intree-tests/ch33-comp-geometry/Test.Segments.fst) | ✅ 6 | ✅ 6 | cross product/intersection |
| 45 | GrahamScan | ch33 | [Test.GrahamScan.fst](intree-tests/ch33-comp-geometry/Test.GrahamScan.fst) | ✅ 3 | ✅ 2 | convex hull |
| 46 | JarvisMarch | ch33 | [Test.JarvisMarch.fst](intree-tests/ch33-comp-geometry/Test.JarvisMarch.fst) | ✅ 2 | ✅ 2 | gift wrapping |
| 47 | VertexCover | ch35 | [Test.VertexCover.fst](intree-tests/ch35-approximation/Test.VertexCover.fst) | ✅ 5 | ✅ 4 | approx cover |

### Summary

- **44/47 algorithms verified** — all soundness and completeness tests pass
- **3 unverified** — InsertionSort, MergeSort, BinarySearch require Pulse (not built)
- **43/47 have completeness tests** — 4 files have only soundness (see below)
- **Verification log**: [`intree-tests/verification-log.txt`](intree-tests/verification-log.txt)

### Completeness Methodology

All completeness tests follow the [Appendix B](https://arxiv.org/abs/2406.09757) pattern:

```
∀y. φ(input, y) ⟹ y == expected
```

Encoded in F* as:

```fstar
let test_complete (y:type) : Lemma
  (requires f input == y)
  (ensures y == expected) = ()
```

**4 files have no completeness tests** — these use `prop` predicates (e.g., `sorted`, `permutation`,
`mutually_compatible`) that assert properties of inputs rather than computing outputs.
Completeness is not applicable because there is no "output" to uniquely determine:

- **CountingSort** — `sorted`, `in_range`, `permutation` are all input properties
- **Quickselect** — `partition_ordered`, `unchanged_outside`, `permutation` are relational props
- **ActivitySelection** — `mutually_compatible` admits multiple valid subsets (not unique)
- **KMP** — `matched_prefix_at` admits multiple valid match positions (q=0 always holds)

**1 file uses inequality bounds** — `SimultaneousMinMax` has `complexity_bounded_minmax_pairs`
with `2*(cf-c0) <= 3*n` (loose bound), so only the tight equality bound gets a completeness test.

### Example: Functional Spec Completeness (GCD)

```fstar
module Test.GCD
open CLRS.Ch31.GCD.Spec

(* Soundness: spec gives correct answer *)
let test_sound_1 () : Lemma (gcd 12 8 == 4) =
  assert_norm (gcd 12 8 == 4)

(* Completeness (Appendix B): output is uniquely determined *)
let test_complete_1 (y:nat) : Lemma
  (requires gcd 12 8 == y)
  (ensures y == 4) =
  assert_norm (gcd 12 8 == 4)
```

### Example: Relational Spec Completeness (InsertionSort)

```fstar
(* Completeness: sorted + permutation uniquely determines output *)
let test_complete (y: Seq.seq int) : Lemma
  (requires sorted y /\ permutation input y)
  (ensures y == expected) = ...  (* proved via count unfolding *)
```

### Technical Patterns

| Pattern | When Used | Example |
|---------|-----------|---------|
| `assert_norm (f x == y)` | Pure computation on concrete inputs | `assert_norm (gcd 12 8 == 4)` |
| `Lemma (requires φ) (ensures y == o)` | Completeness: spec uniquely determines output | `test_complete` in InsertionSort |
| `friend ModuleName` | Abstract `.fsti` functions | Dijkstra (`friend CLRS.Ch24.ShortestPath.Inf`) |
| `reveal_opaque` | Opaque-to-SMT predicates | `permutation` in SortSpec |
| `open Pulse.Lib.BoundedIntegers` | Sorting tests need `<=` | InsertionSort, MergeSort |

## Reproducing Results

### Prerequisites

- Windows with WSL (Ubuntu 24.04) — or native Linux
- F* verifier and Z3 solver built inside WSL

### Setup

```bash
# 1. Install WSL Ubuntu and OCaml toolchain
wsl --install -d Ubuntu
wsl -d Ubuntu -- bash -c "sudo apt-get update && sudo apt-get install -y \
  opam git make pkg-config libgmp-dev"

# 2. Install Z3 4.13.3
wsl -d Ubuntu -- bash -c "
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.13.3/z3-4.13.3-x64-glibc-2.35.zip
  unzip z3-4.13.3-x64-glibc-2.35.zip
  sudo cp z3-4.13.3-x64-glibc-2.35/bin/z3 /usr/local/bin/z3-4.13.3
"

# 3. Clone and build F* from AutoCLRS snapshot
wsl -d Ubuntu -- bash -c "
  cd ~ && git clone --recurse-submodules https://github.com/FStarLang/AutoCLRS.git
  cd AutoCLRS && git checkout 1984af1a9e22c74709293060e649054969f10c2d
  cd fstar && opam init -y && eval \$(opam env)
  opam install --yes ocamlfind batteries stdint zarith yojson fileutils \
    pprint menhir sedlex ppxlib process ppx_deriving ppx_deriving_yojson
  make -j4 -C src/ocaml-output
  make -j4 -C ulib
"

# 4. Copy test files into AutoCLRS and verify
cp -r intree-tests/ch*/ ~/AutoCLRS/autoclrs/
for ch in ~/AutoCLRS/autoclrs/ch*/; do
  echo "=== $ch ==="
  cd "$ch" && FSTAR_EXE=~/AutoCLRS/FStar/bin/fstar.exe make verify && cd -
done
```

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
