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
| **Soundness** | Does φ hold on known-good I/O? | `Lemma (φ(input, output))` |
| **Completeness** (Appendix B) | Does φ uniquely determine the output? | `Lemma (requires x = i ∧ φ(x,y)) (ensures y = o)` |

A specification that is **sound but incomplete** accepts the correct output but also
admits wrong outputs (e.g., "sorted" without "permutation" for sorting).

### Workflow

1. **Generate** — Python produces standalone F* modules encoding the spec + concrete test I/O
2. **Verify** — Each module is checked by F* (via Z3) in WSL
3. **Report** — "All verification conditions discharged" → PASS; otherwise → FAIL

No AI/LLM is used in the evaluation pipeline — only deterministic Python code generation
and the F* verifier.

## AutoCLRS Snapshot

Specifications evaluated against AutoCLRS at commit
[`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d)
(March 2026). See the [AutoCLRS blog post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
for details on the verified CLRS algorithms.

## Evaluation Results

52 algorithms evaluated across 23 CLRS chapters. Each has 3 test cases for
soundness and completeness. See the full [Spec Fidelity Audit Report](SPEC_AUDIT_REPORT.md)
for details on how faithfully each test encodes the actual AutoCLRS postcondition.

**Summary: 52/52 SOUND | 34/52 faithful to AutoCLRS spec (30 complete) | 18/52 weakened spec (under revision)**

### Part 1: Faithful Specs (34 algorithms)

These tests encode the same property as the AutoCLRS postcondition (modulo
complexity bounds, which we intentionally skip). Completeness results are **reliable**.

| # | Algorithm | Ch | AutoCLRS Postcondition | Sound | Complete | Notes |
|---|-----------|-----|----------------------|-------|----------|-------|
| 1 | Insertion Sort | 02 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 2 | Merge Sort | 02 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 3 | Heap Sort | 06 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 4 | Quick Sort | 07 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 5 | Counting Sort | 08 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L625) · [soundness](agent/algorithms.py#L632) · [completeness](agent/algorithms.py#L676) |
| 6 | Radix Sort | 08 | `sorted_multi_digit ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 7 | Bucket Sort | 08 | `sorted ∧ permutation` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L53) · [soundness](agent/algorithms.py#L60) · [completeness](agent/algorithms.py#L95) |
| 8 | GCD | 31 | `result == gcd_spec(a,b)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L155) · [soundness](agent/algorithms.py#L162) · [completeness](agent/algorithms.py#L181) |
| 9 | Extended GCD | 31 | `gcd ∧ a·x+b·y=g` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1466) · [soundness](agent/algorithms.py#L1473) · [completeness](agent/algorithms.py#L1490) |
| 10 | Modular Exp | 31 | `result == mod_exp_spec(b,e,m)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L422) · [soundness](agent/algorithms.py#L429) · [completeness](agent/algorithms.py#L445) |
| 11 | Cross Product | 33 | `result == cross_product_spec(...)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L474) · [soundness](agent/algorithms.py#L481) · [completeness](agent/algorithms.py#L497) |
| 12 | Segment Intersection | 33 | `result == segments_intersect_spec(...)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L529) · [soundness](agent/algorithms.py#L539) · [completeness](agent/algorithms.py#L576) |
| 13 | Minimum | 09 | `∃k. s0[k]==min ∧ ∀k. min≤s0[k]` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1220) · [soundness](agent/algorithms.py#L1227) · [completeness](agent/algorithms.py#L1249) |
| 14 | Maximum | 09 | `∃k. s0[k]==max ∧ ∀k. max≥s0[k]` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1282) · [soundness](agent/algorithms.py#L1289) · [completeness](agent/algorithms.py#L1310) |
| 15 | Min-Max | 09 | min ∧ max simultaneously | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1343) · [soundness](agent/algorithms.py#L1350) · [completeness](agent/algorithms.py#L1372) |
| 16 | Stack (push/pop) | 10 | `pop(push(s,x)) = (x, s)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L744) · [soundness](agent/algorithms.py#L752) · [completeness](agent/algorithms.py#L780) |
| 17 | Queue (enq/deq) | 10 | `dequeue FIFO order` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L817) · [soundness](agent/algorithms.py#L824) · [completeness](agent/algorithms.py#L853) |
| 18 | Linked List Insert | 10 | `is_dlist new_head (x::l)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1710) · [soundness](agent/algorithms.py#L1717) · [completeness](agent/algorithms.py#L1738) |
| 19 | Linked List Delete | 10 | `is_dlist (remove_first k l)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1765) · [soundness](agent/algorithms.py#L1772) · [completeness](agent/algorithms.py#L1801) |
| 20 | Hash Table | 11 | `key_in_table ∧ key_findable` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1835) · [soundness](agent/algorithms.py#L1842) · [completeness](agent/algorithms.py#L1864) |
| 21 | BST Search | 12 | `result == bst_search(ft,k)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1892) · [soundness](agent/algorithms.py#L1899) · [completeness](agent/algorithms.py#L1943) |
| 22 | BST Inorder | 12 | sorted keys from BST | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1990) · [soundness](agent/algorithms.py#L1997) · [completeness](agent/algorithms.py#L2037) |
| 23 | LCS Length | 15 | `result == lcs_length(x,y,m,n)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1030) · [soundness](agent/algorithms.py#L1037) · [completeness](agent/algorithms.py#L1072) |
| 24 | Matrix Chain | 15 | `result == mc_result(dims,n)` | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L2808) · [soundness](agent/algorithms.py#L2815) · [completeness](agent/algorithms.py#L2849) |
| 25 | String Matching | 32 | count_matches correctness | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 26 | KMP String Match | 32 | prefix function correctness | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 27 | Rabin-Karp | 32 | rolling hash match | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L1120) · [soundness](agent/algorithms.py#L1127) · [completeness](agent/algorithms.py#L1166) |
| 28 | Activity Selection | 16 | compatible ∧ maximum count | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L2498) · [soundness](agent/algorithms.py#L2505) · [completeness](agent/algorithms.py#L2549) |
| 29 | Union-Find | 21 | `pure_find` equivalence | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L3116) · [soundness](agent/algorithms.py#L3123) · [completeness](agent/algorithms.py#L3183) |
| 30 | Primality Test | 31 | deterministic is_prime | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L3204) · [soundness](agent/algorithms.py#L3211) · [completeness](agent/algorithms.py#L3240) |
| 31 | Topological Sort | 22 | `all_distinct ∧ is_topological_order` | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid orderings · [tests](agent/algorithms.py#L889) · [soundness](agent/algorithms.py#L899) · [completeness](agent/algorithms.py#L963) |
| 32 | DFS Times | 22 | `d[u]<f[u] ∧ pred_edge_ok` | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — timestamps depend on traversal order · [tests](agent/algorithms.py#L2581) · [soundness](agent/algorithms.py#L2591) · [completeness](agent/algorithms.py#L2625) |
| 33 | Partition (Lomuto) | 07 | `between_bounds ∧ permutation ∧ pivot` | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid partitions · [tests](agent/algorithms.py#L1621) · [soundness](agent/algorithms.py#L1631) · [completeness](agent/algorithms.py#L1669) |
| 34 | Matrix Multiply | 04 | `mat_mul_correct(A,B,C,n)` | ✅ 3/3 | ❌ 0/3 | Z3 can't prove uniqueness · [tests](agent/algorithms.py#L1519) · [soundness](agent/algorithms.py#L1526) · [completeness](agent/algorithms.py#L1568) |

**Faithful completeness: 30/34 pass.** The 4 failures are genuine (non-deterministic output or Z3 limitation).

### Part 2: Weakened Specs (18 algorithms — under revision)

These tests encode a **weaker property** than the actual AutoCLRS postcondition.
Completeness failures may be artifacts of testing a weaker spec. See the
[Spec Fidelity Audit Report](SPEC_AUDIT_REPORT.md) for details on each discrepancy.

| # | Algorithm | Ch | AutoCLRS Spec | What We Test | Gap | Sound | Complete | Source |
|---|-----------|-----|--------------|-------------|-----|-------|----------|--------|
| 35 | Binary Search | 04 | `result==len` for not-found | `r < 0` for not-found | Different convention | ✅ 3/3 | ⚠️ 2/3 | [tests](agent/algorithms.py#L207) · [soundness](agent/algorithms.py#L214) · [completeness](agent/algorithms.py#L250) |
| 36 | Max Subarray | 04 | Pure function `(sum,lo,hi)` | ∃ lo,hi. sum=max ∧ maximal | Effectively equivalent | ✅ 3/3 | ✅ 3/3 | [tests](agent/algorithms.py#L307) · [soundness](agent/algorithms.py#L314) · [completeness](agent/algorithms.py#L365) |
| 37 | Quickselect | 09 | `result == select_spec(s0,k)` | Count-based kth smallest | Missing `select_spec` | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L1403) · [soundness](agent/algorithms.py#L1410) · [completeness](agent/algorithms.py#L1433) |
| 38 | Rod Cutting | 15 | `result == optimal_revenue(prices,n)` | revenue ≥ each piece | Only lower bound | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2081) · [soundness](agent/algorithms.py#L2088) · [completeness](agent/algorithms.py#L2120) |
| 39 | BFS Distance | 22 | `reachable_in(adj,n,src,w,dist[w])` | Triangle inequality-like | Missing reachability | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2148) · [soundness](agent/algorithms.py#L2155) · [completeness](agent/algorithms.py#L2196) |
| 40 | Dijkstra | 24 | `dist[v] == sp_dist(w,n,src,v)` | Triangle inequality | **Much weaker** | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2240) · [soundness](agent/algorithms.py#L2249) · [completeness](agent/algorithms.py#L2295) |
| 41 | Bellman-Ford | 24 | `dist[v] ≤ sp_dist` ∧ triangle | Triangle inequality only | Missing `sp_dist` | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2328) · [soundness](agent/algorithms.py#L2335) · [completeness](agent/algorithms.py#L2376) |
| 42 | Floyd-Warshall | 25 | `contents == fw_outer(c,n,0)` | Triangle inequality | Missing DP equality | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2407) · [soundness](agent/algorithms.py#L2415) · [completeness](agent/algorithms.py#L2460) |
| 43 | DAG Shortest Paths | 24 | `sp_dist` equality | Triangle inequality | Same as Dijkstra | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2944) · [soundness](agent/algorithms.py#L2951) · [completeness](agent/algorithms.py#L2986) |
| 44 | BST Insert | 12 | `bst_subtree == bst_insert(ft,k)` | Sorted inorder ∧ contains | Missing functional spec | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2652) · [soundness](agent/algorithms.py#L2664) · [completeness](agent/algorithms.py#L2700) |
| 45 | BST Delete | 12 | `bst_subtree == bst_delete(ft,k)` | Sorted inorder ∧ removed | Missing functional spec | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2732) · [soundness](agent/algorithms.py#L2739) · [completeness](agent/algorithms.py#L2774) |
| 46 | Huffman Coding | 16 | `cost == greedy_cost ∧ wpl_optimal` | cost ≥ 0 | Only non-negative | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L2887) · [soundness](agent/algorithms.py#L2894) · [completeness](agent/algorithms.py#L2916) |
| 47 | Kruskal MST | 23 | `result_is_forest_adj(edges)` | weight ≥ 0 | Missing forest property | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L3024) · [soundness](agent/algorithms.py#L3031) · [completeness](agent/algorithms.py#L3048) |
| 48 | Prim MST | 23 | `prim_correct(key,parent,w,n,src)` | weight ≥ 0 | Missing MST correctness | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L3070) · [soundness](agent/algorithms.py#L3077) · [completeness](agent/algorithms.py#L3094) |
| 49 | Graham Scan | 33 | `result == find_bottom_spec(xs,ys)` | hull_size bounds | Missing functional spec | ✅ 3/3 | ⚠️ 1/3 | [tests](agent/algorithms.py#L3272) · [soundness](agent/algorithms.py#L3279) · [completeness](agent/algorithms.py#L3297) |
| 50 | Edmonds-Karp | 26 | `valid_flow ∧ no_augmenting_path` | flow ≥ 0 | Missing max-flow property | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L3319) · [soundness](agent/algorithms.py#L3326) · [completeness](agent/algorithms.py#L3355) |
| 51 | Vertex Cover | 35 | Not found in AutoCLRS | cover_size ≤ n | N/A | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L3377) · [soundness](agent/algorithms.py#L3384) · [completeness](agent/algorithms.py#L3401) |
| 52 | Partial Select Sort | 09 | `sorted_prefix ∧ prefix_leq_suffix ∧ perm` | k elements sorted | Missing prefix_leq_suffix | ✅ 3/3 | ❌ 0/3 | [tests](agent/algorithms.py#L3423) · [soundness](agent/algorithms.py#L3430) · [completeness](agent/algorithms.py#L3458) |

## Reproducing Results

### Prerequisites

- Windows with WSL (Ubuntu 24.04) — or native Linux
- Python 3.10+
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
```

### Run

```bash
# All 52 algorithms with 60-second per-test timeout
python agent/run_eval.py --all-algorithms --per-test-timeout 60

# Single algorithm
python agent/run_eval.py --algorithm insertion_sort

# All spec variants for one algorithm
python agent/run_eval.py --algorithm gcd --all-variants
```

### CLI Options

| Flag | Description |
|------|-------------|
| `--algorithm NAME` | Run a single algorithm (default: insertion_sort) |
| `--all-algorithms` | Run all 52 registered algorithms |
| `--spec-variant V` | Evaluate a specific spec variant (default: full) |
| `--all-variants` | Evaluate all spec variants |
| `--per-test-timeout N` | Skip tests exceeding N seconds (default: 60) |
| `--max-tests N` | Limit number of test cases per algorithm |

## How It Works

For each algorithm, `agent/algorithms.py` contains:

1. **Test cases** — 3 small concrete I/O pairs (e.g., `[3,1,2] → [1,2,3]` for sorting)
2. **Soundness generator** — produces an F* module asserting the spec holds on concrete I/O
3. **Completeness generator** — produces an F* module asserting the spec uniquely determines output

`agent/run_eval.py` orchestrates: generate F* → invoke verifier via WSL → collect results.

### Example: Sorting Soundness

```fstar
module IntentEval.InsertionSort.Soundness.Test0
open FStar.Seq
module Seq = FStar.Seq

let input  = Seq.seq_of_list [3; 1; 2]
let output = Seq.seq_of_list [1; 2; 3]

// Spec: sorted ∧ permutation
let soundness_test () : Lemma
  (is_sorted output /\ is_permutation input output)
= ()   // F* + Z3 discharge this automatically
```

### Example: Sorting Completeness (Appendix B)

```fstar
module IntentEval.InsertionSort.Completeness.Test0

let completeness_test (y: Seq.seq int) : Lemma
  (requires is_sorted y /\ is_permutation (Seq.seq_of_list [3; 1; 2]) y)
  (ensures  y == Seq.seq_of_list [1; 2; 3])
= ()   // If F* verifies this, the spec uniquely determines the output
```

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
