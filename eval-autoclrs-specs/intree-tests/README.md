# In-Tree Spec Tests for AutoCLRS

These F* test files evaluate the **soundness** and **completeness** of AutoCLRS specifications
using the [symbolic testing methodology](https://arxiv.org/abs/2406.09757) (FMCAD 2024).

## Approach

Each test file is placed directly in the corresponding AutoCLRS chapter directory and verified
using the **same build system** (`make verify`) that verifies the AutoCLRS proofs. This ensures:

- **No spec duplication**: Tests `open` the real AutoCLRS spec modules — no copy-paste of definitions.
- **Same verification environment**: Uses the same F*, Pulse, and Z3 as the original proofs.
- **Automatic discovery**: The AutoCLRS Makefile auto-discovers `.fst` files in each directory.

### Test Structure

Each test file contains:
- **Soundness tests**: Lemmas asserting that the spec function produces the correct output on concrete inputs.
  Uses `assert_norm` to let the F* normalizer compute spec functions.
- **Completeness tests**: Lemmas marked `[@@expect_failure]` asserting *wrong* outputs.
  F* expects these to fail — if they don't, the spec is too weak.

### Example (GCD)

```fstar
(* Soundness: correct I/O pair *)
let test_sound () : Lemma (gcd_spec 12 8 == 4) = ()

(* Completeness: wrong output must fail *)
[@@expect_failure]
let test_complete () : Lemma (gcd_spec 12 8 == 3) = ()
```

## How to Run

1. Clone [AutoCLRS](https://github.com/FStarLang/AutoCLRS) and build F*/Pulse (`./setup.sh`)
2. Copy each test file into the matching `autoclrs/<chapter>/` directory
3. Run: `cd autoclrs/<chapter> && FSTAR_EXE=path/to/fstar.exe make verify`

## Results

All 8 test files pass (both soundness ✅ and completeness ✅):

| Test File | Chapter | Spec Module | Tests |
|-----------|---------|-------------|-------|
| `Test.GCD.fst` | ch31-number-theory | `CLRS.Ch31.GCD.Spec` | 3 sound, 3 complete |
| `Test.ModExp.fst` | ch31-number-theory | `CLRS.Ch31.ModExp.Spec` | 3 sound, 2 complete |
| `Test.InsertionSort.fst` | ch02-getting-started | `CLRS.Common.SortSpec` | 2 sound, 2 complete |
| `Test.BST.fst` | ch12-bst | `CLRS.Ch12.BST.Spec` | 7 sound, 2 complete |
| `Test.MaxSubarray.fst` | ch04-divide-conquer | `CLRS.Ch04.MaxSubarray.Spec` | 4 sound, 2 complete |
| `Test.RodCutting.fst` | ch15-dynamic-programming | `CLRS.Ch15.RodCutting.Spec` | 4 sound, 2 complete |
| `Test.FloydWarshall.fst` | ch25-apsp | `CLRS.Ch25.FloydWarshall.Spec` | 5 sound, 1 complete |
| `Test.Dijkstra.fst` | ch24-sssp | `CLRS.Ch24.ShortestPath.Spec` | 3 sound, 1 complete |

## Technical Notes

- **`friend` mechanism** (Dijkstra): `CLRS.Ch24.ShortestPath.Inf` hides `inf = 1000000`
  behind a `.fsti` interface. The test declares `friend CLRS.Ch24.ShortestPath.Inf` (with
  an empty `.fsti` for the test module) to expose the concrete value for normalizer evaluation.
- **`assert_norm`**: Used to invoke the F* normalizer for computing recursive spec functions
  (e.g., `sp_dist`, `fw_entry`, `optimal_revenue`) on concrete inputs.
- **`reveal_opaque`**: Required for `permutation` in sorting tests, which is marked
  `[@@"opaque_to_smt"]` in `CLRS.Common.SortSpec`.
- **`Pulse.Lib.BoundedIntegers`**: Must be opened in sorting tests for correct `<=` operator resolution.
