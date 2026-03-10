# Spec Fidelity Audit Report

Audit of how faithfully our symbolic tests encode the actual AutoCLRS F*
postconditions for each of the 52 algorithms.

**AutoCLRS snapshot:** commit [`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d)

## Summary

| Category | Count | Soundness | Completeness |
|----------|-------|-----------|--------------|
| **Faithful to AutoCLRS spec** | 34 | 34/34 ✅ | 30/34 (4 genuinely incomplete) |
| **Weakened / Approximated spec** | 18 | 18/18 ✅ | 1/18 (results unreliable) |
| **Total** | 52 | 52/52 ✅ | 31/52 |

---

## Part 1: Faithful Specs (34 algorithms)

These tests encode the same property as the AutoCLRS postcondition (modulo
complexity bounds, which we intentionally skip). Completeness results for
these are **reliable**.

| # | Algorithm | Ch | AutoCLRS Postcondition | Our Encoding | Sound | Complete | Notes |
|---|-----------|-----|----------------------|--------------|-------|----------|-------|
| 1 | Insertion Sort | 02 | `sorted s ∧ permutation s0 s` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 2 | Merge Sort | 02 | `sorted s ∧ permutation s0 s` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 3 | Heap Sort | 06 | `sorted s ∧ permutation s0 s` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 4 | Quick Sort | 07 | `sorted s ∧ permutation s0 s` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 5 | Counting Sort | 08 | `sorted ∧ permutation` | sorted ∧ permutation ∧ in_range | ✅ 3/3 | ✅ 3/3 | |
| 6 | Radix Sort | 08 | `sorted_multi_digit ∧ permutation` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 7 | Bucket Sort | 08 | `sorted ∧ permutation` | sorted ∧ permutation | ✅ 3/3 | ✅ 3/3 | |
| 8 | GCD | 31 | `result == gcd_spec(a,b)` | divides(g,a) ∧ divides(g,b) ∧ greatest | ✅ 3/3 | ✅ 3/3 | Relational equivalent |
| 9 | Extended GCD | 31 | `extended_gcd` pure function | gcd(a,b)=g ∧ a·x+b·y=g | ✅ 3/3 | ✅ 3/3 | |
| 10 | Modular Exp | 31 | `result == mod_exp_spec(b,e,m)` | result == b^e mod m | ✅ 3/3 | ✅ 3/3 | |
| 11 | Cross Product | 33 | `result == cross_product_spec(...)` | r = (p2−p1) × (p3−p1) | ✅ 3/3 | ✅ 3/3 | |
| 12 | Segment Intersection | 33 | `result == segments_intersect_spec(...)` | orientation-based test | ✅ 3/3 | ✅ 3/3 | |
| 13 | Minimum | 09 | `∃k. s0[k]==min ∧ ∀k. min≤s0[k]` | m=min(arr) ∧ m∈arr | ✅ 3/3 | ✅ 3/3 | |
| 14 | Maximum | 09 | `∃k. s0[k]==max ∧ ∀k. max≥s0[k]` | m=max(arr) ∧ m∈arr | ✅ 3/3 | ✅ 3/3 | |
| 15 | Min-Max | 09 | min ∧ max simultaneously | min ∧ max simultaneously | ✅ 3/3 | ✅ 3/3 | |
| 16 | Stack (push/pop) | 10 | `pop(push(s,x)) = (x, s)` | pop(push(s,x)) = (x, s) | ✅ 3/3 | ✅ 3/3 | |
| 17 | Queue (enq/deq) | 10 | `dequeue FIFO order` | dequeue FIFO | ✅ 3/3 | ✅ 3/3 | |
| 18 | Linked List Insert | 10 | `is_dlist new_head (x::l)` | head=new ∧ tail=old | ✅ 3/3 | ✅ 3/3 | |
| 19 | Linked List Delete | 10 | `is_dlist new_head (remove_first k l)` | element removed, rest preserved | ✅ 3/3 | ✅ 3/3 | |
| 20 | Hash Table | 11 | `key_in_table ∧ key_findable` | key mod table_size | ✅ 3/3 | ✅ 3/3 | |
| 21 | BST Search | 12 | `result == bst_search(ft,k)` | found⇒key in tree, ¬found⇒key∉tree | ✅ 3/3 | ✅ 3/3 | |
| 22 | BST Inorder | 12 | sorted keys from BST | sorted keys from BST | ✅ 3/3 | ✅ 3/3 | |
| 23 | LCS Length | 15 | `result == lcs_length(x,y,m,n)` | r == lcs_length recursive | ✅ 3/3 | ✅ 3/3 | |
| 24 | Matrix Chain | 15 | `result == mc_result(dims,n)` | min scalar multiplications | ✅ 3/3 | ✅ 3/3 | |
| 25 | String Matching | 32 | count_matches correctness | count_matches | ✅ 3/3 | ✅ 3/3 | |
| 26 | KMP String Match | 32 | prefix function correctness | count_matches | ✅ 3/3 | ✅ 3/3 | |
| 27 | Rabin-Karp | 32 | rolling hash match | count_matches | ✅ 3/3 | ✅ 3/3 | |
| 28 | Activity Selection | 16 | `activity_selection_post` (compatible ∧ max) | max compatible non-overlapping | ✅ 3/3 | ✅ 3/3 | |
| 29 | Union-Find | 21 | `pure_find` equivalence | connected matches union ops | ✅ 3/3 | ✅ 3/3 | |
| 30 | Primality Test | 31 | deterministic is_prime | is_prime deterministic | ✅ 3/3 | ✅ 3/3 | |
| 31 | Topological Sort | 22 | `all_distinct ∧ is_topological_order` | valid topo order ∧ all_distinct | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid orderings |
| 32 | DFS Times | 22 | `d[u]<f[u] ∧ pred_edge_ok` | d[v]<f[v] ∧ parenthesis | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — timestamps depend on traversal order |
| 33 | Partition (Lomuto) | 07 | `between_bounds ∧ permutation ∧ pivot` | elements ≤pivot before, >pivot after | ✅ 3/3 | ❌ 0/3 | **Genuinely incomplete** — multiple valid partitions |
| 34 | Matrix Multiply | 04 | `mat_mul_correct(A,B,C,n)` | C[i,j]=dot(A_row_i, B_col_j) | ✅ 3/3 | ❌ 0/3 | Z3 can't prove uniqueness |

### Faithful Completeness Failures (4 algorithms)

| Algorithm | Reason | Genuine? |
|-----------|--------|----------|
| Topological Sort | Multiple valid orderings exist for any DAG | ✅ Yes — spec is inherently non-deterministic |
| DFS Times | Discovery/finish timestamps depend on traversal order | ✅ Yes — spec is inherently non-deterministic |
| Partition | Multiple valid partitioned arrays exist | ✅ Yes — spec is inherently non-deterministic |
| Matrix Multiply | Spec is likely complete but Z3 can't prove it | ⚠️ Z3 limitation |

---

## Part 2: Weakened / Approximated Specs (18 algorithms)

These tests encode a **weaker property** than the actual AutoCLRS postcondition.
Completeness failures may be artifacts of the weakened spec, not genuine findings.

| # | Algorithm | Ch | AutoCLRS Postcondition | What We Test Instead | Fidelity Issue | Sound | Complete |
|---|-----------|-----|----------------------|---------------------|----------------|-------|----------|
| 35 | Binary Search | 04 | `result==idx` or `result==len` (not found) | `r < 0` for not-found | Different not-found convention | ✅ 3/3 | ⚠️ 2/3 |
| 36 | Max Subarray | 04 | Pure function `(sum, lo, hi)` | ∃ lo,hi. sum=max ∧ maximal | Effectively equivalent | ✅ 3/3 | ✅ 3/3 |
| 37 | Quickselect | 09 | `result == select_spec(s0,k)` ∧ permutation ∧ partitioned | Count-based kth smallest | Missing `select_spec` and partitioned array | ✅ 3/3 | ❌ 0/3 |
| 38 | Rod Cutting | 15 | `result == optimal_revenue(prices,n)` | revenue ≥ each piece price | Only checks lower bound, not optimality | ✅ 3/3 | ❌ 0/3 |
| 39 | BFS Distance | 22 | `reachable_in(adj,n,src,w,dist[w])` | Triangle inequality-like | Missing exact reachability predicate | ✅ 3/3 | ❌ 0/3 |
| 40 | Dijkstra | 24 | `dist[v] == sp_dist(weights,n,src,v)` | Triangle inequality only | **Much weaker** — relaxation ≠ shortest path | ✅ 3/3 | ❌ 0/3 |
| 41 | Bellman-Ford | 24 | `dist[v] ≤ sp_dist` ∧ `triangle_inequality` | Triangle inequality only | Missing `sp_dist` upper bound | ✅ 3/3 | ❌ 0/3 |
| 42 | Floyd-Warshall | 25 | `contents == fw_outer(contents,n,0)` | Triangle inequality | Missing DP fixed-point equality | ✅ 3/3 | ❌ 0/3 |
| 43 | DAG Shortest Paths | 24 | `sp_dist` equality | Triangle inequality | Same as Dijkstra | ✅ 3/3 | ❌ 0/3 |
| 44 | BST Insert | 12 | `bst_subtree == bst_insert(ft,k)` | Sorted inorder ∧ contains key | Missing functional `bst_insert` | ✅ 3/3 | ❌ 0/3 |
| 45 | BST Delete | 12 | `bst_subtree == bst_delete(ft,k)` | Sorted inorder ∧ key removed | Missing functional `bst_delete` | ✅ 3/3 | ❌ 0/3 |
| 46 | Huffman Coding | 16 | `cost == greedy_cost` ∧ `is_wpl_optimal` | cost ≥ 0 | Only checks non-negative, not optimality | ✅ 3/3 | ❌ 0/3 |
| 47 | Kruskal MST | 23 | `result_is_forest_adj(edges)` | weight ≥ 0 | Missing forest/spanning-tree property | ✅ 3/3 | ❌ 0/3 |
| 48 | Prim MST | 23 | `prim_correct(key,parent,weights,n,src)` | weight ≥ 0 | Missing MST correctness | ✅ 3/3 | ❌ 0/3 |
| 49 | Graham Scan | 33 | `result == find_bottom_spec(xs,ys)` | hull_size bounds | Missing functional spec | ✅ 3/3 | ⚠️ 1/3 |
| 50 | Edmonds-Karp | 26 | `valid_flow ∧ no_augmenting_path` | flow ≥ 0 ∧ capacities ≥ 0 | Missing max-flow-min-cut property | ✅ 3/3 | ❌ 0/3 |
| 51 | Vertex Cover | 35 | Not found in AutoCLRS | cover_size ≤ n | May not exist in AutoCLRS | ✅ 3/3 | ❌ 0/3 |
| 52 | Partial Select Sort | 09 | `sorted_prefix ∧ prefix_leq_suffix ∧ permutation` | k elements sorted only | Missing `prefix_leq_suffix` and permutation | ✅ 3/3 | ❌ 0/3 |

### Severity of Weakening

| Severity | Count | Algorithms |
|----------|-------|-----------|
| **Trivially weak** (only checks bounds/non-negative) | 6 | Huffman, Kruskal, Prim, Graham Scan, Edmonds-Karp, Vertex Cover |
| **Missing key predicate** (partial spec) | 7 | Rod Cutting, Quickselect, BFS, BST Insert, BST Delete, Partial Select Sort, Binary Search |
| **Fundamentally different property** | 4 | Dijkstra, Bellman-Ford, Floyd-Warshall, DAG SP |
| **Effectively equivalent** | 1 | Max Subarray |

---

## Conclusions

1. **Soundness is reliable across all 52 algorithms** — a weaker spec is still implied by the true spec, so soundness results are valid.

2. **Completeness is reliable for 34/52** (the faithful specs):
   - 30/34 pass completeness ✅
   - 4/34 are genuinely incomplete (non-deterministic output or Z3 limitation)

3. **Completeness is unreliable for 18/52** (weakened specs):
   - Only 1/18 passes (Max Subarray, which is effectively equivalent)
   - The 17 failures may be artifacts of testing a weaker property

4. **Next step:** Import actual AutoCLRS spec modules to fix the 18 weakened encodings and get reliable completeness results.
