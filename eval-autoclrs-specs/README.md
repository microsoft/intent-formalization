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
- Import **only** the `Impl` module — no spec modules exposed
- Assert the output equals a concrete expected value
- The test verifies iff the postcondition (spec) is strong enough to prove `y == expected`

All AutoCLRS implementations are Pulse, so all tests use `#lang-pulse`.

## AutoCLRS Submodule

AutoCLRS is included as a git submodule at `eval-autoclrs-specs/autoclrs/`,
pinned to commit [`1984af1`](https://github.com/FStarLang/AutoCLRS/tree/1984af1a9e22c74709293060e649054969f10c2d).

## Evaluation Results

| # | Algorithm | Ch | Impl Function | Test File | Status | Notes |
|---|-----------|-----|--------------|-----------|--------|-------|
| 1 | Quicksort | ch07 | `quicksort` | [Test.Quicksort.fst](intree-tests/ch07-quicksort/Test.Quicksort.fst) | ✅ | Verified with F*+Pulse |

### Example: Quicksort Completeness Test

The `quicksort` implementation has the postcondition:
```
ensures exists* s. (A.pts_to a s ** pure (sorted s /\ permutation s0 s))
```
i.e., the output is **sorted** and a **permutation** of the input.

The completeness test:
1. Creates input array `[3, 1, 2]`
2. Calls `quicksort arr 3sz` (the Pulse implementation)
3. Proves the output must be `[1, 2, 3]` via a completeness lemma
4. Reads each element and asserts `v0 == 1`, `v1 == 2`, `v2 == 3`

The completeness lemma works by:
- Revealing the opaque `permutation` predicate to expose `FStar.Seq.Properties.permutation`
- Using `count`-based reasoning: since `[3,1,2]` has exactly one copy of each element, any sorted permutation must be `[1,2,3]`
- Bridging `BoundedIntegers` typeclass operators (`<=`) to standard `Prims.op_LessThanOrEqual` for Z3

```fstar
(* Pure helper: sorted + permutation of [3;1;2] uniquely determines [1;2;3] *)
let std_sort3 (s: Seq.seq int)
  : Lemma
    (requires (forall (i j:nat). Prims.op_LessThanOrEqual i j /\
                                 Prims.op_LessThan j (Seq.length s) ==>
                                 Prims.op_LessThanOrEqual (Seq.index s i) (Seq.index s j)) /\
              SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= SP.perm_len (Seq.seq_of_list [3; 1; 2]) s;
  assert_norm (SP.count 1 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 2 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 3 (Seq.seq_of_list [3; 1; 2]) == 1);
  assert_norm (SP.count 0 (Seq.seq_of_list [3; 1; 2]) == 0);
  assert_norm (SP.count 4 (Seq.seq_of_list [3; 1; 2]) == 0)

(* Bridges BoundedIntegers typeclass operators to Prims operators *)
let completeness_sort3 (s: Seq.seq int)
  : Lemma
    (requires SS.sorted s /\ SP.permutation int (Seq.seq_of_list [3; 1; 2]) s)
    (ensures Seq.index s 0 == 1 /\ Seq.index s 1 == 2 /\ Seq.index s 2 == 3)
= assert (forall (i j:nat). (i <= j) == Prims.op_LessThanOrEqual i j);
  assert (forall (x y:int). (x <= y) == Prims.op_LessThanOrEqual x y);
  std_sort3 s
```

The Pulse test then calls the implementation and uses the lemma:
```pulse
fn test_quicksort_3 ()
  requires emp
  ensures emp
{
  // Setup input [3; 1; 2]
  ...
  arr.(0sz) <- 3; arr.(1sz) <- 1; arr.(2sz) <- 2;

  // y = quicksort(x)
  quicksort arr 3sz;

  // assert(y == expected)
  with s. assert (A.pts_to arr s);
  reveal_opaque (`%SS.permutation) (SS.permutation s0 s);
  completeness_sort3 s;

  let v0 = arr.(0sz); let v1 = arr.(1sz); let v2 = arr.(2sz);
  assert (pure (v0 == 1));  // ✅ F* proves this
  assert (pure (v1 == 2));  // ✅ F* proves this
  assert (pure (v2 == 3));  // ✅ F* proves this
  ...
}
```

### Verification

Tests are verified using the AutoCLRS build system (`make verify`), which invokes
F* with the Pulse plugin for `#lang-pulse` files.

```bash
# From the autoclrs/autoclrs/ch07-quicksort/ directory:
make verify
```

This requires a working F* + Pulse build (see [setup.sh](autoclrs/setup.sh) in the submodule).

**Current status:** ✅ Quicksort completeness test verified with F* + Pulse plugin.

```
$ make verify
   CHECK           Test.Quicksort.fst
   Verified module: Test.Quicksort
   All verification conditions discharged successfully
```

## References

- [Lahiri, "Evaluating LLM-driven User-Intent Formalization for Verification-Aware Languages", FMCAD 2024](https://arxiv.org/abs/2406.09757)
- [AutoCLRS: Verified CLRS Algorithms in F*](https://github.com/FStarLang/AutoCLRS)
- [AutoCLRS Blog Post](https://risemsr.github.io/blog/2026-03-06-autoclrs/)
- [Intent Formalization Blog Post](https://risemsr.github.io/blog/2026-03-05-shuvendu-intent-formalization/)
