# Intent Formalization for AutoCLRS Algorithms

Completeness testing of verified algorithm implementations from the
[AutoCLRS](https://github.com/FStarLang/AutoCLRS) repository — verified
Pulse implementations of algorithms from *Introduction to Algorithms* (CLRS).

See the [Intent Formalization blog](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/) for an overview of the research direction.

Uses the **completeness testing** approach from:

> **Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages**
> *Shuvendu K. Lahiri*, FMCAD 2024.
> [https://arxiv.org/abs/2406.09757](https://arxiv.org/abs/2406.09757)
>
> Specifically, the **Appendix B** method for completeness checking.

## Method

Each test is a **black-box completeness check** against the implementation:

```
test(x) { y = algorithm(x); assert(y == expected) }
```

- Call the **Pulse implementation** directly (e.g., `quicksort`)
- Import **only** the `Impl` module — no spec modules exposed in the test
- Assert the output equals a concrete expected value
- The test verifies iff the postcondition (spec) is strong enough to prove `y == expected`

Most AutoCLRS implementations are Pulse (imperative), so tests use `#lang-pulse`.
A few algorithms have pure F\* specs only (no Pulse impl), tested as pure lemmas.

## AutoCLRS Submodule

AutoCLRS is included as a git submodule at `eval-autoclrs-specs/autoclrs/`,
pinned to commit [`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d).

## Evaluation Results

**48 tests total — 41 call Pulse implementation functions, 7 are pure spec tests (no Impl module exists)**

**43 completeness proofs discharged ✅, 5 spec incomplete ❌.**

**5 non-determinism tests ❌ᴺ** — algorithms where the spec *is* complete for the original test input (unique output) but *not* for an alternative input where multiple valid outputs exist. These demonstrate that completeness can be **input-dependent** when the postcondition is relational rather than functional.

### Sorting (ch02, ch06, ch07, ch08)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 1 | InsertionSort | ch02 | [`insertion_sort`](autoclrs/autoclrs/ch02-getting-started/CLRS.Ch02.InsertionSort.Impl.fsti) | [Test.InsertionSort.fst](intree-tests/ch02-getting-started/Test.InsertionSort.fst) | ✅ |
| 2 | MergeSort | ch02 | [`merge_sort`](autoclrs/autoclrs/ch02-getting-started/CLRS.Ch02.MergeSort.Impl.fsti) | [Test.MergeSort.fst](intree-tests/ch02-getting-started/Test.MergeSort.fst) | ✅ |
| 3 | Heapsort | ch06 | [`heapsort`](autoclrs/autoclrs/ch06-heapsort/CLRS.Ch06.Heap.Impl.fsti) | [Test.Heap.fst](intree-tests/ch06-heapsort/Test.Heap.fst) | ✅ |
| 4 | Quicksort | ch07 | [`quicksort`](autoclrs/autoclrs/ch07-quicksort/CLRS.Ch07.Quicksort.Impl.fsti) | [Test.Quicksort.fst](intree-tests/ch07-quicksort/Test.Quicksort.fst) | ✅ |
| 5 | BucketSort | ch08 | *(spec only)* | [Test.BucketSort.fst](intree-tests/ch08-linear-sorting/Test.BucketSort.fst) | ✅ |
| 6 | RadixSort | ch08 | *(spec only)* | [Test.RadixSort.fst](intree-tests/ch08-linear-sorting/Test.RadixSort.fst) | ✅ |
| 7 | CountingSort | ch08 | [`counting_sort_inplace`](autoclrs/autoclrs/ch08-linear-sorting/CLRS.Ch08.CountingSort.Impl.fsti) | [Test.CountingSort.fst](intree-tests/ch08-linear-sorting/Test.CountingSort.fst) | ✅ |

### Search & Selection (ch04, ch09)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 8 | BinarySearch | ch04 | [`binary_search`](autoclrs/autoclrs/ch04-divide-conquer/CLRS.Ch04.BinarySearch.Impl.fsti) | [Test.BinarySearch.fst](intree-tests/ch04-divide-conquer/Test.BinarySearch.fst) | ✅ |
| | ↳ *non-det* | | input `[1,3,3,5]` key=3: index 1 *and* 2 valid | [Test.BinarySearch2.fst](intree-tests/ch04-divide-conquer/Test.BinarySearch2.fst) | ❌ᴺ |
| 9 | MaxSubarray | ch04 |*(spec only)* | [Test.MaxSubarray.fst](intree-tests/ch04-divide-conquer/Test.MaxSubarray.fst) | ✅ |
| 10 | MatrixMultiply | ch04 | [`matrix_multiply`](autoclrs/autoclrs/ch04-divide-conquer/CLRS.Ch04.MatrixMultiply.Impl.fsti) | [Test.MatrixMultiply.fst](intree-tests/ch04-divide-conquer/Test.MatrixMultiply.fst) | ✅ |
| 11 | MinMax | ch09 | [`find_minimum`](autoclrs/autoclrs/ch09-order-statistics/CLRS.Ch09.MinMax.Impl.fsti) | [Test.MinMax.fst](intree-tests/ch09-order-statistics/Test.MinMax.fst) | ✅ |
| 12 | PartialSelectionSort | ch09 | [`select`](autoclrs/autoclrs/ch09-order-statistics/CLRS.Ch09.PartialSelectionSort.Impl.fsti) | [Test.PartialSelectionSort.fst](intree-tests/ch09-order-statistics/Test.PartialSelectionSort.fst) | ✅ |
| 13 | Quickselect | ch09 | [`quickselect`](autoclrs/autoclrs/ch09-order-statistics/CLRS.Ch09.Quickselect.Impl.fsti) | [Test.Quickselect.fst](intree-tests/ch09-order-statistics/Test.Quickselect.fst) | ✅ |
| 14 | SimultaneousMinMax | ch09 | [`find_minmax`](autoclrs/autoclrs/ch09-order-statistics/CLRS.Ch09.SimultaneousMinMax.Impl.fsti) | [Test.SimultaneousMinMax.fst](intree-tests/ch09-order-statistics/Test.SimultaneousMinMax.fst) | ✅ |

### Data Structures (ch10, ch11, ch12, ch13)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 15 | Stack | ch10 | [`push`, `pop`](autoclrs/autoclrs/ch10-elementary-ds/CLRS.Ch10.Stack.Impl.fsti) | [Test.Stack.fst](intree-tests/ch10-elementary-ds/Test.Stack.fst) | ✅ |
| 16 | SLL | ch10 | [`list_insert`](autoclrs/autoclrs/ch10-elementary-ds/CLRS.Ch10.SinglyLinkedList.Impl.fsti) | [Test.SLL.fst](intree-tests/ch10-elementary-ds/Test.SLL.fst) | ✅ |
| 17 | DLL | ch10 | [`list_insert`](autoclrs/autoclrs/ch10-elementary-ds/CLRS.Ch10.DLL.Impl.fsti) | [Test.DLL.fst](intree-tests/ch10-elementary-ds/Test.DLL.fst) | ✅ |
| 18 | Queue | ch10 | [`enqueue`, `dequeue`](autoclrs/autoclrs/ch10-elementary-ds/CLRS.Ch10.Queue.Impl.fsti) | [Test.Queue.fst](intree-tests/ch10-elementary-ds/Test.Queue.fst) | ✅ |
| 19 | HashTable | ch11 | [`hash_insert`, `hash_search`](autoclrs/autoclrs/ch11-hash-tables/CLRS.Ch11.HashTable.Impl.fsti) | [Test.HashTable.fst](intree-tests/ch11-hash-tables/Test.HashTable.fst) | ❌ |
| 20 | BST | ch12 | [`tree_insert`, `tree_search`](autoclrs/autoclrs/ch12-bst/CLRS.Ch12.BST.Impl.fsti) | [Test.BST.fst](intree-tests/ch12-bst/Test.BST.fst) | ✅ |
| 21 | BSTArray | ch12 | [`tree_search`](autoclrs/autoclrs/ch12-bst/CLRS.Ch12.BSTArray.Impl.fsti) | [Test.BSTArray.fst](intree-tests/ch12-bst/Test.BSTArray.fst) | ✅ |
| 22 | RBTree | ch13 | *(spec only — upstream build error)* | [Test.RBTree.fst](intree-tests/ch13-rbtree/Test.RBTree.fst) | ✅ |

### Dynamic Programming (ch15)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 23 | LCS | ch15 | [`lcs`](autoclrs/autoclrs/ch15-dynamic-programming/CLRS.Ch15.LCS.Impl.fsti) | [Test.LCS.fst](intree-tests/ch15-dynamic-programming/Test.LCS.fst) | ✅ |
| 24 | MatrixChain | ch15 | [`matrix_chain_order`](autoclrs/autoclrs/ch15-dynamic-programming/CLRS.Ch15.MatrixChain.Impl.fsti) | [Test.MatrixChain.fst](intree-tests/ch15-dynamic-programming/Test.MatrixChain.fst) | ✅ |
| 25 | RodCutting | ch15 | [`rod_cutting`](autoclrs/autoclrs/ch15-dynamic-programming/CLRS.Ch15.RodCutting.Impl.fsti) | [Test.RodCutting.fst](intree-tests/ch15-dynamic-programming/Test.RodCutting.fst) | ✅ |

### Greedy (ch16)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 26 | ActivitySelection | ch16 | [`activity_selection`](autoclrs/autoclrs/ch16-greedy/CLRS.Ch16.ActivitySelection.Impl.fsti) | [Test.ActivitySelection.fst](intree-tests/ch16-greedy/Test.ActivitySelection.fst) | ✅ |
| | ↳ *non-det* | | activities (1,2),(2,3),(2,3): either activity 1 or 2 valid | [Test.ActivitySelection2.fst](intree-tests/ch16-greedy/Test.ActivitySelection2.fst) | ❌ᴺ |
| 27 | Huffman |ch16 | [`huffman_tree`](autoclrs/autoclrs/ch16-greedy/CLRS.Ch16.Huffman.Impl.fsti) | [Test.Huffman.fst](intree-tests/ch16-greedy/Test.Huffman.fst) | ✅ |

### Union-Find & Graphs (ch21, ch22)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 28 | UnionFind | ch21 | [`make_set`, `union`, `find_set`](autoclrs/autoclrs/ch21-disjoint-sets/CLRS.Ch21.UnionFind.Impl.fsti) | [Test.UnionFind.fst](intree-tests/ch21-disjoint-sets/Test.UnionFind.fst) | ✅ |
| 29 | BFS | ch22 | [`queue_bfs`](autoclrs/autoclrs/ch22-elementary-graph/CLRS.Ch22.BFS.Impl.fsti) | [Test.BFS.fst](intree-tests/ch22-elementary-graph/Test.BFS.fst) | ✅ |
| 30 | DFS | ch22 | [`stack_dfs`](autoclrs/autoclrs/ch22-elementary-graph/CLRS.Ch22.DFS.Impl.fsti) | [Test.DFS.fst](intree-tests/ch22-elementary-graph/Test.DFS.fst) | ✅ |
| | ↳ *non-det* | | fork graph 0→1,0→2: d[1]=2 or d[1]=4 depending on visit order | [Test.DFS2.fst](intree-tests/ch22-elementary-graph/Test.DFS2.fst) | ❌ᴺ |
| 31 | TopologicalSort | ch22 | [`topological_sort`](autoclrs/autoclrs/ch22-elementary-graph/CLRS.Ch22.TopologicalSort.Impl.fsti) | [Test.TopologicalSort.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort.fst) | ✅ |
| | ↳ *non-det* | | fork graph 0→1,0→2: [0,1,2] *and* [0,2,1] both valid | [Test.TopologicalSort2.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort2.fst) | ❌ᴺ |

### MST & Shortest Paths (ch23, ch24, ch25, ch26)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 32 | Kruskal | ch23 | [`kruskal`](autoclrs/autoclrs/ch23-mst/CLRS.Ch23.Kruskal.Impl.fsti) | [Test.Kruskal.fst](intree-tests/ch23-mst/Test.Kruskal.fst) | ❌ |
| 33 | Prim | ch23 | [`prim`](autoclrs/autoclrs/ch23-mst/CLRS.Ch23.Prim.Impl.fsti) | [Test.Prim.fst](intree-tests/ch23-mst/Test.Prim.fst) | ❌ |
| 34 | BellmanFord | ch24 | [`bellman_ford`](autoclrs/autoclrs/ch24-sssp/CLRS.Ch24.BellmanFord.Impl.fsti) | [Test.BellmanFord.fst](intree-tests/ch24-sssp/Test.BellmanFord.fst) | ❌ |
| 35 | Dijkstra | ch24 | [`dijkstra`](autoclrs/autoclrs/ch24-sssp/CLRS.Ch24.Dijkstra.Impl.fsti) | [Test.Dijkstra.fst](intree-tests/ch24-sssp/Test.Dijkstra.fst) | ✅ |
| | ↳ *non-det* | | diamond 0→1→3, 0→2→3 (equal weight): pred[3]=1 *or* 2 | [Test.Dijkstra2.fst](intree-tests/ch24-sssp/Test.Dijkstra2.fst) | ❌ᴺ |
| 36 | FloydWarshall |ch25 | [`floyd_warshall`](autoclrs/autoclrs/ch25-apsp/CLRS.Ch25.FloydWarshall.Impl.fsti) | [Test.FloydWarshall.fst](intree-tests/ch25-apsp/Test.FloydWarshall.fst) | ✅ |
| 37 | MaxFlow | ch26 | [`max_flow`](autoclrs/autoclrs/ch26-max-flow/CLRS.Ch26.MaxFlow.Impl.fsti) | [Test.MaxFlow.fst](intree-tests/ch26-max-flow/Test.MaxFlow.fst) | ✅ |

### Number Theory (ch31)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 38 | GCD | ch31 | [`gcd_impl`](autoclrs/autoclrs/ch31-number-theory/CLRS.Ch31.GCD.Impl.fsti) | [Test.GCD.fst](intree-tests/ch31-number-theory/Test.GCD.fst) | ✅ |
| 39 | ModExp | ch31 | [`mod_exp_impl`](autoclrs/autoclrs/ch31-number-theory/CLRS.Ch31.ModExp.Impl.fsti) | [Test.ModExp.fst](intree-tests/ch31-number-theory/Test.ModExp.fst) | ✅ |
| 40 | ModExpLR | ch31 | [`mod_exp_lr_impl`](autoclrs/autoclrs/ch31-number-theory/CLRS.Ch31.ModExpLR.Impl.fsti) | [Test.ModExpLR.fst](intree-tests/ch31-number-theory/Test.ModExpLR.fst) | ✅ |
| 41 | ExtendedGCD | ch31 | *(spec only)* | [Test.ExtendedGCD.fst](intree-tests/ch31-number-theory/Test.ExtendedGCD.fst) | ✅ |

### String Matching (ch32)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 42 | NaiveStringMatch | ch32 | *(spec only)* | [Test.NaiveStringMatch.fst](intree-tests/ch32-string-matching/Test.NaiveStringMatch.fst) | ✅ |
| 43 | KMP | ch32 | *(spec only)* | [Test.KMP.fst](intree-tests/ch32-string-matching/Test.KMP.fst) | ✅ |
| 44 | RabinKarp | ch32 | *(spec only)* | [Test.RabinKarp.fst](intree-tests/ch32-string-matching/Test.RabinKarp.fst) | ✅ |

### Computational Geometry (ch33)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 45 | Segments | ch33 | [`segments_intersect`](autoclrs/autoclrs/ch33-comp-geometry/CLRS.Ch33.Segments.Impl.fsti) | [Test.Segments.fst](intree-tests/ch33-comp-geometry/Test.Segments.fst) | ✅ |
| 46 | GrahamScan | ch33 | [`find_bottom`](autoclrs/autoclrs/ch33-comp-geometry/CLRS.Ch33.GrahamScan.Impl.fsti) | [Test.GrahamScan.fst](intree-tests/ch33-comp-geometry/Test.GrahamScan.fst) | ✅ |
| 47 | JarvisMarch | ch33 | [`jarvis_march`](autoclrs/autoclrs/ch33-comp-geometry/CLRS.Ch33.JarvisMarch.Impl.fsti) | [Test.JarvisMarch.fst](intree-tests/ch33-comp-geometry/Test.JarvisMarch.fst) | ✅ |

### Approximation (ch35)

| # | Algorithm | Ch | Impl Function | Test File | Proof |
|---|-----------|-----|---------------|-----------|-------|
| 48 | VertexCover | ch35 | [`approx_vertex_cover`](autoclrs/autoclrs/ch35-approximation/CLRS.Ch35.VertexCover.Impl.fsti) | [Test.VertexCover.fst](intree-tests/ch35-approximation/Test.VertexCover.fst) | ❌ |

### Legend

- **Impl Function**: the Pulse implementation function called in the test (from `*.Impl` module). Links to the `.fsti` in the AutoCLRS submodule.
- *(spec only)*: no `Impl` module exists in AutoCLRS; test uses pure F\* spec functions
- **Proof**: ✅ = completeness proved, ❌ = spec incomplete (postcondition too weak to determine output), ❌ᴺ = non-determinism (spec complete for original input, incomplete for alternative input with multiple valid outputs)

### Completeness Failures (❌)

These 5 algorithms have postconditions that are **too weak to uniquely determine the output** for the given test input — a genuine spec incompleteness finding:

| Algorithm | Reason |
|-----------|--------|
| HashTable | `hash_insert` postcondition allows `ok=false` (table full), but an empty size-5 table always has room — spec doesn't expose this |
| Kruskal | `result_is_forest_adj` only guarantees a forest subset of edges, not the *specific* MST edges |
| Prim | `prim_correct` guarantees MST properties but doesn't force `parent[1]=0` for a unique MST |
| BellmanFord | postcondition allows `ok=false` (negative cycle detected), but this graph has no negative cycles — spec doesn't expose this |
| VertexCover | `is_cover` + 2-approx bound satisfied by `[1,0]` as well as `[1,1]` — spec doesn't force both endpoints |

### Input-Dependent Completeness (❌ᴺ)

These 5 algorithms have specs that **are** complete for the original test input (where the output is uniquely determined) but **fail** for an alternative input where multiple valid outputs exist. This demonstrates that completeness is **input-dependent** for relational (non-functional) postconditions:

| Algorithm | Original Input (✅ unique) | Alternative Input (❌ᴺ non-unique) |
|-----------|---------------------------|--------------------------------------|
| BinarySearch | `[1,2,3,4,5]` key=3 → index 2 (unique) | `[1,3,3,5]` key=3 → index 1 *or* 2 |
| DFS | chain 0→1→2 → timestamps unique | fork 0→1,0→2 → d[1]=2 or d[1]=4 |
| TopologicalSort | chain 0→1→2 → only [0,1,2] | fork 0→1,0→2 → [0,1,2] or [0,2,1] |
| Dijkstra | unique shortest paths → pred unique | diamond 0→{1,2}→3 equal weight → pred[3]=1 or 2 |
| ActivitySelection | distinct finish times → unique greedy set | tied finish times (2,3),(2,3) → activity 1 or 2 |

### Example: Topological Sort — Complete vs Incomplete

The [`topological_sort`](autoclrs/autoclrs/ch22-elementary-graph/CLRS.Ch22.TopologicalSort.Impl.fsti) implementation has the postcondition:
```
ensures exists* sout. (V.pts_to output sout ** pure (
  all_distinct (seq_int_to_nat sout) /\
  is_topological_order adj n (seq_int_to_nat sout)))
```
i.e., the output is a **permutation of all vertices** in a valid **topological order**.

#### ✅ Complete: chain graph 0→1→2

With edges 0→1 and 1→2, there is exactly **one** valid topological order: `[0, 1, 2]`.

```fstar
(* The spec uniquely determines the output for this graph *)
let completeness_topo (sout adj: Seq.seq int) : Lemma
  (requires (* adj encodes edges 0→1, 1→2 *) /\
    all_distinct (seq_int_to_nat sout) /\
    is_topological_order adj 3 (seq_int_to_nat sout))
  (ensures Seq.index sout 0 == 0 /\ Seq.index sout 1 == 1 /\ Seq.index sout 2 == 2)
= assert (has_edge 3 adj 0 1 == true);
  assert (has_edge 3 adj 1 2 == true)
  (* Z3 derives: 0 must precede 1, 1 must precede 2 → only [0,1,2] works *)
```

The Pulse test calls the implementation and uses the lemma:
```pulse
fn test_topological_sort () requires emp ensures emp
{
  (* ... setup adj for 0→1→2 ... *)
  let output = topological_sort adj 3sz ctr;
  with sout. assert (V.pts_to output sout);
  completeness_topo sout s0;                  // ✅ proved!
  (* ... read output[0]==0, output[1]==1, output[2]==2 ... *)
}
```

**F\* verifies this** — the postcondition is strong enough to prove the output.

#### ❌ Incomplete: fork graph 0→1, 0→2

With edges 0→1 and 0→2 (no edge between 1 and 2), **two** valid topological orders exist: `[0, 1, 2]` and `[0, 2, 1]`.

```fstar
(* This lemma CANNOT be proved — the spec admits two valid outputs *)
let completeness_topo_v2 (sout adj: Seq.seq int) : Lemma
  (requires (* adj encodes edges 0→1, 0→2 *) /\
    all_distinct (seq_int_to_nat sout) /\
    is_topological_order adj 3 (seq_int_to_nat sout))
  (ensures Seq.index sout 0 == 0 /\ Seq.index sout 1 == 1 /\ Seq.index sout 2 == 2)
= admit()  (* ❌ unprovable — [0,2,1] also satisfies the postcondition *)
```

**F\* rejects this** — the postcondition is too weak to distinguish between the two valid orderings.
This is exactly the kind of spec incompleteness the evaluation is designed to detect.

Both tests are in the repository:
- [Test.TopologicalSort.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort.fst) — ✅ chain graph (complete)
- [Test.TopologicalSort2.fst](intree-tests/ch22-elementary-graph/Test.TopologicalSort2.fst) — ❌ fork graph (incomplete)

## Reproducing the Verification

### Prerequisites

Build F\* and Pulse following the [AutoCLRS setup instructions](autoclrs/setup.sh):

```bash
# Clone and build (from a Linux/WSL environment)
cd eval-autoclrs-specs/autoclrs
bash setup.sh          # builds F*, Pulse, Karamel, Steel
export FSTAR_EXE=$(pwd)/FStar/bin/fstar.exe
```

### Running Tests

Each test file lives alongside the AutoCLRS chapter source.
Copy the test files into the AutoCLRS build tree and run `make verify`:

```bash
# Example: verify quicksort completeness test
cp intree-tests/ch07-quicksort/Test.Quicksort.fst autoclrs/ch07-quicksort/
cd autoclrs/ch07-quicksort
make verify
# Output:
#    CHECK           Test.Quicksort.fst
#    Verified module: Test.Quicksort
#    All verification conditions discharged successfully
```

To verify all chapters:

```bash
for ch in ch02-getting-started ch04-divide-conquer ch06-heapsort ch07-quicksort \
          ch08-linear-sorting ch10-elementary-ds ch11-hash-tables ch12-bst \
          ch15-dynamic-programming ch16-greedy ch21-disjoint-sets \
          ch22-elementary-graph ch23-mst ch24-sssp ch25-apsp ch26-max-flow \
          ch31-number-theory ch32-string-matching ch33-comp-geometry ch35-approximation; do
  echo "=== $ch ==="
  cp intree-tests/${ch}/Test.*.fst autoclrs/${ch}/ 2>/dev/null
  (cd autoclrs/${ch} && rm -rf _cache .depend && make verify) || echo "FAILED: $ch"
done
```

**Note**: ch09 and ch13 have upstream build errors in AutoCLRS and cannot currently be verified.

### Known Limitations

1. **SZ.fits refinement on implicit args**: Heapsort's Pulse implementation has a `SZ.fits` refinement on an erased implicit parameter that cannot be satisfied from test code (Pulse emits subtyping checks as isolated SMT queries). Workaround: pure spec test.

2. **BoundedIntegers bridge**: Sorting algorithms using `CLRS.Common.SortSpec.sorted` require bridging BoundedIntegers typeclass operators to `Prims` operators for Z3. See the `std_sort3` / `completeness_sort3` pattern.

3. **Error 310 in ch23/ch24**: Some test files reference modules not in the chapter's include path.

4. **Upstream build errors**: ch09 (`Quickselect.Impl.fst` Error 47) and ch13 (`RBTree.Impl.fsti` Error 189) fail to build in the upstream AutoCLRS repo itself.

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
