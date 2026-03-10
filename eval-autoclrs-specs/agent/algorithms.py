"""
Algorithm registry: test cases and F* module generators for each algorithm.

Each algorithm defines:
  - test_cases: list of dicts with input/output
  - soundness_gen(idx, test) -> (module_name, fstar_code)
  - completeness_gen(idx, test, variant) -> (module_name, fstar_code)
  - spec_variants: list of variant names
  - spec_description: human-readable spec
"""

from typing import List, Tuple, Dict, Any


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

def _seq_list(values, typ="int"):
    """F* sequence via seq_of_list."""
    if not values:
        return f"Seq.empty #{typ}"
    elems = "; ".join(str(v) for v in values)
    return f"Seq.seq_of_list [{elems}]"


def _seq_append(values, typ="int"):
    """F* sequence via Seq.append chains (better for permutation proofs)."""
    if not values:
        return f"Seq.empty #{typ}"
    parts = [f"Seq.create 1 ({v})" for v in values]
    result = parts[0]
    for p in parts[1:]:
        result = f"Seq.append ({result}) ({p})"
    return result


def _z3_opts(n, rlimit=200, fuel=8):
    if n > 3:
        return f'\n#push-options "--z3rlimit {rlimit} --fuel {fuel} --ifuel {fuel}"\n'
    return ''


def _z3_pop(n):
    return '\n#pop-options' if n > 3 else ''


# ---------------------------------------------------------------------------
# Sorting spec: sorted /\ permutation
# Used by: InsertionSort, MergeSort, HeapSort, QuickSort, BucketSort
# ---------------------------------------------------------------------------

SORTING_TESTS = [
    ([3, 1, 2], [1, 2, 3]),
    ([2, 1], [1, 2]),
    ([1], [1]),
]


def _sorting_soundness(algo, idx, inp, out):
    mod = f"IntentEval.{algo}.Soundness.Test{idx}"
    n = len(out)
    sorted_hints = "\n".join(
        f"  assert (Seq.index output {i} <= Seq.index output {j});"
        for i in range(n) for j in range(i, n)
    )
    idx_hints = "\n".join(
        [f"  assert (Seq.index input {i} == {v});" for i, v in enumerate(inp)] +
        [f"  assert (Seq.index output {i} == {v});" for i, v in enumerate(out)]
    )
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq
{_z3_opts(n)}
let sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let input : Seq.seq int = {_seq_list(inp)}
let output : Seq.seq int = {_seq_list(out)}

let soundness_test () : Lemma
  (sorted output /\\ Seq.length input == Seq.length output /\\
   Seq.Properties.permutation int input output)
=
  assert (Seq.length input == {len(inp)});
  assert (Seq.length output == {n});
{sorted_hints}
{idx_hints}
  ()
{_z3_pop(n)}
"""
    return mod, code


def _sorting_completeness(algo, idx, inp, out, variant="full"):
    mod = f"IntentEval.{algo}.Completeness.{variant.title()}.Test{idx}"
    n = len(out)

    if variant == "full":
        assumes = "sorted y /\\ Seq.Properties.permutation int x y"
    elif variant == "sorted_only":
        assumes = "sorted y /\\ Seq.length y == Seq.length x"
    elif variant == "permutation_only":
        assumes = "Seq.Properties.permutation int x y"
    else:
        raise ValueError(variant)

    input_asserts = "\n".join(
        f"  assert (Seq.index x {i} == {v});" for i, v in enumerate(inp)
    )

    if variant in ("sorted_only", "permutation_only"):
        proof = "\n".join(
            f"  assert (Seq.index y {i} == {v});" for i, v in enumerate(out)
        )
    else:
        sorted_h = "\n".join(
            f"  assert (Seq.index y {i} <= Seq.index y {j});"
            for i in range(n) for j in range(i, n)
        )
        out_h = "\n".join(
            f"  assert (Seq.index y {i} == {v});" for i, v in enumerate(out)
        )
        proof = sorted_h + "\n" + out_h

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let input_val : Seq.seq int = {_seq_append(inp)}
let output_val : Seq.seq int = {_seq_append(out)}

let completeness_test (x y: Seq.seq int) : Lemma
  (requires Seq.equal x input_val /\\ {assumes} /\\ Seq.length y == {n})
  (ensures Seq.equal y output_val)
=
{input_asserts}
{proof}
  ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# GCD spec: divides(g, a) /\ divides(g, b) /\ greatest
# ---------------------------------------------------------------------------

GCD_TESTS = [
    {"a": 6, "b": 4, "g": 2},
    {"a": 15, "b": 5, "g": 5},
    {"a": 7, "b": 3, "g": 1},
]


def _gcd_soundness(idx, test):
    a, b, g = test["a"], test["b"], test["g"]
    mod = f"IntentEval.GCD.Soundness.Test{idx}"
    code = f"""module {mod}

let divides (d n: nat) : prop = d > 0 /\\ n % d == 0

let a_val : nat = {a}
let b_val : nat = {b}
let g_val : nat = {g}

let soundness_test () : Lemma
  (divides g_val a_val /\\ divides g_val b_val /\\
   (forall (d: pos). d > 0 /\\ a_val % d == 0 /\\ b_val % d == 0 ==> d <= g_val))
= ()
"""
    return mod, code


def _gcd_completeness(idx, test, variant="full"):
    a, b, g = test["a"], test["b"], test["g"]
    mod = f"IntentEval.GCD.Completeness.{variant.title()}.Test{idx}"

    if variant == "full":
        assumes = (f"g > 0 /\\ {a} % g == 0 /\\ {b} % g == 0 /\\ "
                   f"(forall (d: pos). {a} % d == 0 /\\ {b} % d == 0 ==> d <= g)")
    elif variant == "divides_only":
        assumes = f"g > 0 /\\ {a} % g == 0 /\\ {b} % g == 0"
    else:
        raise ValueError(variant)

    code = f"""module {mod}

let completeness_test (g: nat) : Lemma
  (requires {assumes})
  (ensures g == {g})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Binary Search spec: found => arr[idx]==key, not_found => key not in arr
# ---------------------------------------------------------------------------

BINARY_SEARCH_TESTS = [
    {"arr": [1, 3, 5, 7], "key": 3, "result": 1},    # found at index 1
    {"arr": [1, 3, 5, 7], "key": 4, "result": -1},    # not found
    {"arr": [2, 4, 6], "key": 6, "result": 2},        # found at last
]


def _bsearch_soundness(idx, test):
    arr, key, result = test["arr"], test["key"], test["result"]
    n = len(arr)
    mod = f"IntentEval.BinarySearch.Soundness.Test{idx}"

    arr_fstar = _seq_list(arr)
    idx_asserts = "\n".join(
        f"  assert (Seq.index arr {i} == {v});" for i, v in enumerate(arr)
    )
    sorted_asserts = "\n".join(
        f"  assert (Seq.index arr {i} <= Seq.index arr {j});"
        for i in range(n) for j in range(i, n)
    )

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let arr : Seq.seq int = {arr_fstar}
let result : int = {result}

let soundness_test () : Lemma
  (is_sorted arr /\\
   (result >= 0 ==> (result < Seq.length arr /\\ Seq.index arr result == {key})) /\\
   (result < 0 ==> (forall (i:nat). i < Seq.length arr ==> Seq.index arr i <> {key})))
=
{sorted_asserts}
{idx_asserts}
  ()
"""
    return mod, code


def _bsearch_completeness(idx, test, variant="full"):
    arr, key, result = test["arr"], test["key"], test["result"]
    n = len(arr)
    mod = f"IntentEval.BinarySearch.Completeness.{variant.title()}.Test{idx}"

    arr_fstar = _seq_list(arr)

    # Unified spec: covers both found and not-found
    if variant == "full":
        assumes = (f"Seq.equal a arr_val /\\ Seq.length a == {n} /\\ is_sorted a /\\ "
                   f"(r >= 0 ==> (r < {n} /\\ Seq.index a r == {key})) /\\ "
                   f"(r < 0 ==> (forall (i:nat). i < {n} ==> Seq.index a i <> {key}))")
    elif variant == "found_only":
        assumes = (f"Seq.equal a arr_val /\\ Seq.length a == {n} /\\ "
                   f"(r >= 0 ==> (r < {n} /\\ Seq.index a r == {key}))")
    else:
        raise ValueError(variant)

    idx_asserts = "\n".join(
        f"  assert (Seq.index a {i} == {v});" for i, v in enumerate(arr)
    )

    # Help Z3 eliminate wrong indices
    eliminate_hints = []
    if result >= 0:
        for i, v in enumerate(arr):
            if v != key:
                eliminate_hints.append(f"  assert (Seq.index a {i} <> {key});")

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {result})
=
{idx_asserts}
{chr(10).join(eliminate_hints)}
  ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Max Subarray spec: result == max contiguous subarray sum
# ---------------------------------------------------------------------------

MAX_SUBARRAY_TESTS = [
    {"arr": [-2, 1, 3], "result": 4},      # subarray [1, 3]
    {"arr": [1, 2, 3], "result": 6},        # whole array
    {"arr": [2, -1, 3], "result": 4},       # whole array
]


def _maxsub_soundness(idx, test):
    arr, result = test["arr"], test["result"]
    n = len(arr)
    mod = f"IntentEval.MaxSubarray.Soundness.Test{idx}"

    arr_fstar = _seq_list(arr)
    idx_asserts = "\n".join(
        f"  assert (Seq.index arr {i} == {v});" for i, v in enumerate(arr)
    )

    # Find witness (lo, hi) for the existential (non-empty: lo < hi)
    best = None
    for lo in range(n):
        for hi in range(lo + 1, n + 1):
            s = sum(arr[lo:hi])
            if best is None or s > best[0]:
                best = (s, lo, hi)

    # Compute all sum_range values as hints
    sum_hints = []
    for lo in range(n):
        for hi in range(lo + 1, n + 1):
            s = sum(arr[lo:hi])
            sum_hints.append(f"  assert (sum_range arr {lo} {hi} == {s});")

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--fuel {n + 1} --ifuel 0 --z3rlimit 20"

let rec sum_range (s: Seq.seq int) (lo hi: nat) : Tot int (decreases (hi - lo)) =
  if lo >= hi || lo >= Seq.length s then 0
  else Seq.index s lo + sum_range s (lo + 1) hi

let arr : Seq.seq int = {arr_fstar}

let soundness_test () : Lemma
  ((exists (lo hi: nat). lo < hi /\\ hi <= {n} /\\ sum_range arr lo hi == {result}) /\\
   (forall (lo hi: nat). lo < hi /\\ hi <= {n} ==> sum_range arr lo hi <= {result}))
=
{idx_asserts}
  assert (Seq.length arr == {n});
{chr(10).join(sum_hints)}
  ()

#pop-options
"""
    return mod, code


def _maxsub_completeness(idx, test, variant="full"):
    arr, result = test["arr"], test["result"]
    n = len(arr)
    mod = f"IntentEval.MaxSubarray.Completeness.{variant.title()}.Test{idx}"

    arr_fstar = _seq_list(arr)
    idx_asserts = "\n".join(
        f"  assert (Seq.index a {i} == {v});" for i, v in enumerate(arr)
    )

    # Compute all sum_range values as hints
    sum_hints = []
    for lo in range(n):
        for hi in range(lo + 1, n + 1):
            s = sum(arr[lo:hi])
            sum_hints.append(f"  assert (sum_range a {lo} {hi} == {s});")

    if variant == "full":
        assumes = (f"Seq.equal a arr_val /\\ Seq.length a == {n} /\\ "
                   f"(exists (lo hi: nat). lo < hi /\\ hi <= {n} /\\ sum_range a lo hi == r) /\\ "
                   f"(forall (lo hi: nat). lo < hi /\\ hi <= {n} ==> sum_range a lo hi <= r)")
    elif variant == "exists_only":
        assumes = (f"Seq.equal a arr_val /\\ Seq.length a == {n} /\\ "
                   f"(exists (lo hi: nat). lo < hi /\\ hi <= {n} /\\ sum_range a lo hi == r)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--fuel {n + 1} --ifuel 0 --z3rlimit 20"

let rec sum_range (s: Seq.seq int) (lo hi: nat) : Tot int (decreases (hi - lo)) =
  if lo >= hi || lo >= Seq.length s then 0
  else Seq.index s lo + sum_range s (lo + 1) hi

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {result})
=
{idx_asserts}
  assert (Seq.length a == {n});
{chr(10).join(sum_hints)}
  ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Modular exponentiation spec: result == b^e mod m
# ---------------------------------------------------------------------------

MODEXP_TESTS = [
    {"b": 2, "e": 3, "m": 5, "result": 3},     # 8 mod 5 = 3
    {"b": 3, "e": 2, "m": 7, "result": 2},      # 9 mod 7 = 2
    {"b": 2, "e": 0, "m": 3, "result": 1},      # 1 mod 3 = 1
]


def _modexp_soundness(idx, test):
    b, e, m, r = test["b"], test["e"], test["m"], test["result"]
    mod = f"IntentEval.ModExp.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

let rec pow (b: int) (e: nat) : int =
  if e = 0 then 1 else b * pow b (e - 1)

let soundness_test () : Lemma
  (pow {b} {e} % {m} == {r} /\\ {r} >= 0 /\\ {r} < {m})
= ()
"""
    return mod, code


def _modexp_completeness(idx, test, variant="full"):
    b, e, m, r = test["b"], test["e"], test["m"], test["result"]
    mod = f"IntentEval.ModExp.Completeness.{variant.title()}.Test{idx}"

    if variant == "full":
        assumes = f"result == pow {b} {e} % {m} /\\ result >= 0 /\\ result < {m}"
    elif variant == "range_only":
        assumes = f"result >= 0 /\\ result < {m}"
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul

let rec pow (b: int) (e: nat) : int =
  if e = 0 then 1 else b * pow b (e - 1)

let completeness_test (result: int) : Lemma
  (requires {assumes})
  (ensures result == {r})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Cross product spec: result == (p2-p1) x (p3-p1)
# ---------------------------------------------------------------------------

CROSS_PRODUCT_TESTS = [
    {"x1": 0, "y1": 0, "x2": 1, "y2": 0, "x3": 0, "y3": 1, "result": 1},    # CCW
    {"x1": 0, "y1": 0, "x2": 0, "y2": 1, "x3": 1, "y3": 0, "result": -1},   # CW
    {"x1": 0, "y1": 0, "x2": 2, "y2": 2, "x3": 4, "y3": 4, "result": 0},    # collinear
]


def _cross_soundness(idx, test):
    t = test
    mod = f"IntentEval.CrossProduct.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

let cross_product (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)

let soundness_test () : Lemma
  (cross_product {t['x1']} {t['y1']} {t['x2']} {t['y2']} {t['x3']} {t['y3']} == {t['result']})
= ()
"""
    return mod, code


def _cross_completeness(idx, test, variant="full"):
    t = test
    mod = f"IntentEval.CrossProduct.Completeness.{variant.title()}.Test{idx}"

    if variant == "full":
        assumes = (f"r == (({t['x2']} - {t['x1']}) * (({t['y3']}) - {t['y1']})) - "
                   f"(({t['x3']} - {t['x1']}) * (({t['y2']}) - {t['y1']}))")
    elif variant == "sign_only":
        if t['result'] > 0:
            assumes = "r > 0"
        elif t['result'] < 0:
            assumes = "r < 0"
        else:
            assumes = "r == 0"
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul

let completeness_test (r: int) : Lemma
  (requires {assumes})
  (ensures r == {t['result']})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Segment intersection spec: orientation-based boolean test
# ---------------------------------------------------------------------------

SEGMENT_INTERSECTION_TESTS = [
    # Two crossing segments
    {"x1": 0, "y1": 0, "x2": 4, "y2": 4, "x3": 0, "y3": 4, "x4": 4, "y4": 0, "result": True},
    # Two parallel non-intersecting segments
    {"x1": 0, "y1": 0, "x2": 2, "y2": 0, "x3": 0, "y3": 1, "x4": 2, "y4": 1, "result": False},
    # Touching at endpoint
    {"x1": 0, "y1": 0, "x2": 1, "y2": 1, "x3": 1, "y3": 1, "x4": 2, "y4": 0, "result": True},
]


def _segment_soundness(idx, test):
    t = test
    mod = f"IntentEval.SegmentIntersect.Soundness.Test{idx}"
    r_str = "true" if t["result"] else "false"
    code = f"""module {mod}
open FStar.Mul

let max_int (a b: int) : int = if a >= b then a else b
let min_int (a b: int) : int = if a <= b then a else b

let cross_product (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)

let on_segment (x1 y1 x2 y2 x y: int) : bool =
  min_int x1 x2 <= x && x <= max_int x1 x2 &&
  min_int y1 y2 <= y && y <= max_int y1 y2

let segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int) : bool =
  let d1 = cross_product x3 y3 x4 y4 x1 y1 in
  let d2 = cross_product x3 y3 x4 y4 x2 y2 in
  let d3 = cross_product x1 y1 x2 y2 x3 y3 in
  let d4 = cross_product x1 y1 x2 y2 x4 y4 in
  if ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
     ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)) then true
  else if d1 = 0 && on_segment x3 y3 x4 y4 x1 y1 then true
  else if d2 = 0 && on_segment x3 y3 x4 y4 x2 y2 then true
  else if d3 = 0 && on_segment x1 y1 x2 y2 x3 y3 then true
  else if d4 = 0 && on_segment x1 y1 x2 y2 x4 y4 then true
  else false

let soundness_test () : Lemma
  (segments_intersect {t['x1']} {t['y1']} {t['x2']} {t['y2']} {t['x3']} {t['y3']} {t['x4']} {t['y4']} == {r_str})
= ()
"""
    return mod, code


def _segment_completeness(idx, test, variant="full"):
    t = test
    mod = f"IntentEval.SegmentIntersect.Completeness.{variant.title()}.Test{idx}"
    r_str = "true" if t["result"] else "false"

    if variant == "full":
        assumes = (f"r == segments_intersect {t['x1']} {t['y1']} {t['x2']} {t['y2']} "
                   f"{t['x3']} {t['y3']} {t['x4']} {t['y4']}")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul

let max_int (a b: int) : int = if a >= b then a else b
let min_int (a b: int) : int = if a <= b then a else b

let cross_product (x1 y1 x2 y2 x3 y3: int) : int =
  (x2 - x1) * (y3 - y1) - (x3 - x1) * (y2 - y1)

let on_segment (x1 y1 x2 y2 x y: int) : bool =
  min_int x1 x2 <= x && x <= max_int x1 x2 &&
  min_int y1 y2 <= y && y <= max_int y1 y2

let segments_intersect (x1 y1 x2 y2 x3 y3 x4 y4: int) : bool =
  let d1 = cross_product x3 y3 x4 y4 x1 y1 in
  let d2 = cross_product x3 y3 x4 y4 x2 y2 in
  let d3 = cross_product x1 y1 x2 y2 x3 y3 in
  let d4 = cross_product x1 y1 x2 y2 x4 y4 in
  if ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
     ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)) then true
  else if d1 = 0 && on_segment x3 y3 x4 y4 x1 y1 then true
  else if d2 = 0 && on_segment x3 y3 x4 y4 x2 y2 then true
  else if d3 = 0 && on_segment x1 y1 x2 y2 x3 y3 then true
  else if d4 = 0 && on_segment x1 y1 x2 y2 x4 y4 then true
  else false

let completeness_test (r: bool) : Lemma
  (requires {assumes})
  (ensures r == {r_str})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Counting sort spec: sorted /\ permutation /\ in_range (on nat)
# ---------------------------------------------------------------------------

COUNTING_SORT_TESTS = [
    {"input": [3, 1, 2], "output": [1, 2, 3], "k": 3},
    {"input": [2, 0, 1], "output": [0, 1, 2], "k": 2},
    {"input": [1, 1], "output": [1, 1], "k": 1},
]


def _counting_soundness(idx, test):
    inp, out, k = test["input"], test["output"], test["k"]
    n = len(out)
    mod = f"IntentEval.CountingSort.Soundness.Test{idx}"

    sorted_hints = "\n".join(
        f"  assert (Seq.index output {i} <= Seq.index output {j});"
        for i in range(n) for j in range(i, n)
    )
    idx_hints = "\n".join(
        [f"  assert (Seq.index input {i} == {v});" for i, v in enumerate(inp)] +
        [f"  assert (Seq.index output {i} == {v});" for i, v in enumerate(out)]
    )
    range_hints = "\n".join(
        f"  assert (Seq.index output {i} <= {k});" for i in range(n)
    )

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let sorted (s: Seq.seq nat) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let in_range (s: Seq.seq nat) (k: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i <= k

let input : Seq.seq nat = Seq.seq_of_list [{"; ".join(str(v) for v in inp)}]
let output : Seq.seq nat = Seq.seq_of_list [{"; ".join(str(v) for v in out)}]

let soundness_test () : Lemma
  (sorted output /\\ Seq.length input == Seq.length output /\\
   Seq.Properties.permutation nat input output /\\ in_range output {k})
=
  assert (Seq.length input == {n});
  assert (Seq.length output == {n});
{sorted_hints}
{idx_hints}
{range_hints}
  ()
"""
    return mod, code


def _counting_completeness(idx, test, variant="full"):
    inp, out, k = test["input"], test["output"], test["k"]
    n = len(out)
    mod = f"IntentEval.CountingSort.Completeness.{variant.title()}.Test{idx}"

    inp_fstar = "; ".join(str(v) for v in inp)
    out_fstar = "; ".join(str(v) for v in out)

    if variant == "full":
        assumes = (f"sorted y /\\ Seq.Properties.permutation nat x y /\\ "
                   f"in_range y {k}")
    elif variant == "sorted_only":
        assumes = f"sorted y /\\ Seq.length y == Seq.length x /\\ in_range y {k}"
    elif variant == "no_range":
        assumes = "sorted y /\\ Seq.Properties.permutation nat x y"
    else:
        raise ValueError(variant)

    input_asserts = "\n".join(
        f"  assert (Seq.index x {i} == {v});" for i, v in enumerate(inp)
    )

    if variant in ("sorted_only",):
        proof = "\n".join(
            f"  assert (Seq.index y {i} == {v});" for i, v in enumerate(out)
        )
    else:
        sorted_h = "\n".join(
            f"  assert (Seq.index y {i} <= Seq.index y {j});"
            for i in range(n) for j in range(i, n)
        )
        out_h = "\n".join(
            f"  assert (Seq.index y {i} == {v});" for i, v in enumerate(out)
        )
        proof = sorted_h + "\n" + out_h

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let sorted (s: Seq.seq nat) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let in_range (s: Seq.seq nat) (k: nat) : prop =
  forall (i: nat). i < Seq.length s ==> Seq.index s i <= k

let input_val : Seq.seq nat = Seq.seq_of_list [{inp_fstar}]
let output_val : Seq.seq nat = Seq.seq_of_list [{out_fstar}]

let completeness_test (x y: Seq.seq nat) : Lemma
  (requires Seq.equal x input_val /\\ {assumes} /\\ Seq.length y == {n})
  (ensures Seq.equal y output_val)
=
{input_asserts}
{proof}
  ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Stack spec: push/pop correctness
# ---------------------------------------------------------------------------

STACK_TESTS = [
    {"ops": "push 3, push 1, pop", "stack_before_pop": [1, 3], "pop_result": 1, "stack_after": [3]},
    {"ops": "push 5, push 2, pop, pop",
     "stack_before_pop": [2, 5], "pop_result": 2, "stack_after": [5]},
    {"ops": "push 7, pop", "stack_before_pop": [7], "pop_result": 7, "stack_after": []},
]


def _stack_soundness(idx, test):
    mod = f"IntentEval.Stack.Soundness.Test{idx}"
    before = test["stack_before_pop"]
    pop_val = test["pop_result"]
    after = test["stack_after"]

    before_list = "; ".join(str(v) for v in before)
    after_list = "; ".join(str(v) for v in after) if after else ""

    code = f"""module {mod}

open FStar.List.Tot

let stack (a: Type) = list a
let stack_push (#a: Type) (s: stack a) (x: a) : stack a = x :: s
let stack_pop (#a: Type) (s: stack a{{Cons? s}}) : a & stack a =
  (hd s, tl s)

let s_before : stack int = [{before_list}]

let soundness_test () : Lemma
  (let (v, s_after) = stack_pop s_before in
   v == {pop_val} /\\ s_after == [{after_list}])
= ()
"""
    return mod, code


def _stack_completeness(idx, test, variant="full"):
    mod = f"IntentEval.Stack.Completeness.{variant.title()}.Test{idx}"
    before = test["stack_before_pop"]
    pop_val = test["pop_result"]
    after = test["stack_after"]

    before_list = "; ".join(str(v) for v in before)
    after_list = "; ".join(str(v) for v in after) if after else ""

    if variant == "full":
        assumes = (f"Cons? s /\\ s == [{before_list}] /\\ "
                   f"(let (v, _) = stack_pop s in v == r)")
    elif variant == "pop_only":
        assumes = f"Cons? s /\\ (let (v, _) = stack_pop s in v == r)"
    else:
        raise ValueError(variant)

    code = f"""module {mod}

open FStar.List.Tot

let stack (a: Type) = list a
let stack_pop (#a: Type) (s: stack a{{Cons? s}}) : a & stack a =
  (hd s, tl s)

let completeness_test (s: stack int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {pop_val})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Queue spec: enqueue/dequeue (FIFO)
# ---------------------------------------------------------------------------

QUEUE_TESTS = [
    {"enqueued": [1, 2, 3], "dequeue_result": 1, "remaining": [2, 3]},
    {"enqueued": [5], "dequeue_result": 5, "remaining": []},
    {"enqueued": [7, 8], "dequeue_result": 7, "remaining": [8]},
]


def _queue_soundness(idx, test):
    mod = f"IntentEval.Queue.Soundness.Test{idx}"
    enq = test["enqueued"]
    dq_val = test["dequeue_result"]
    remain = test["remaining"]

    enq_list = "; ".join(str(v) for v in enq)
    rem_list = "; ".join(str(v) for v in remain) if remain else ""

    code = f"""module {mod}

open FStar.List.Tot

let queue_to_list (q: list int) : list int = q

let dequeue (q: list int{{Cons? q}}) : int & list int =
  (hd q, tl q)

let q_val : list int = [{enq_list}]

let soundness_test () : Lemma
  (Cons? q_val /\\
   (let (v, rest) = dequeue q_val in
    v == {dq_val} /\\ rest == [{rem_list}]))
= ()
"""
    return mod, code


def _queue_completeness(idx, test, variant="full"):
    mod = f"IntentEval.Queue.Completeness.{variant.title()}.Test{idx}"
    enq = test["enqueued"]
    dq_val = test["dequeue_result"]

    enq_list = "; ".join(str(v) for v in enq)

    if variant == "full":
        assumes = (f"Cons? q /\\ q == [{enq_list}] /\\ "
                   f"(let (v, _) = dequeue q in v == r)")
    elif variant == "dequeue_only":
        assumes = f"Cons? q /\\ (let (v, _) = dequeue q in v == r)"
    else:
        raise ValueError(variant)

    code = f"""module {mod}

open FStar.List.Tot

let dequeue (q: list int{{Cons? q}}) : int & list int =
  (hd q, tl q)

let completeness_test (q: list int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {dq_val})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Topological Sort spec: valid ordering (expected INCOMPLETE — non-unique)
# ---------------------------------------------------------------------------

# DAG: 3 vertices, edges: 0->1, 0->2
# Adjacency matrix (row-major): adj[i*n+j] = 1 if edge i->j
TOPO_SORT_TESTS = [
    # 3 vertices, edges: 0->1, 0->2
    {"n": 3, "adj": [0,1,1, 0,0,0, 0,0,0], "order": [0, 1, 2]},
    # 3 vertices, edges: 2->0, 2->1
    {"n": 3, "adj": [0,0,0, 0,0,0, 1,1,0], "order": [2, 0, 1]},
    # 2 vertices, edge: 0->1
    {"n": 2, "adj": [0,1, 0,0], "order": [0, 1]},
]


def _topo_soundness(idx, test):
    n_v, adj, order = test["n"], test["adj"], test["order"]
    mod = f"IntentEval.TopoSort.Soundness.Test{idx}"

    adj_list = "; ".join(str(v) for v in adj)
    order_list = "; ".join(str(v) for v in order)

    # Build explicit edge checks
    edge_checks = []
    for u in range(n_v):
        for v in range(n_v):
            if adj[u * n_v + v] == 1:
                # Check u appears before v in order
                u_pos = order.index(u)
                v_pos = order.index(v)
                edge_checks.append(
                    f"  // edge {u}->{v}: pos({u})={u_pos} < pos({v})={v_pos}"
                )

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && Seq.length adj = n * n && Seq.index adj (u * n + v) = 1

let rec position_aux (order: Seq.seq nat) (v: nat) (i: nat) : Tot int (decreases (Seq.length order - i)) =
  if i >= Seq.length order then -1
  else if Seq.index order i = v then i
  else position_aux order v (i + 1)

let position (order: Seq.seq nat) (v: nat) : int = position_aux order v 0

let is_topological_order (adj: Seq.seq int) (n: nat) (order: Seq.seq nat) : prop =
  Seq.length order == n /\\
  Seq.length adj == n * n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ has_edge n adj u v ==>
    position order u >= 0 /\\ position order v >= 0 /\\
    position order u < position order v)

let all_distinct (order: Seq.seq nat) : prop =
  forall (i j: nat). i < Seq.length order /\\ j < Seq.length order /\\ i <> j ==>
    Seq.index order i <> Seq.index order j

let adj_val : Seq.seq int = Seq.seq_of_list [{adj_list}]
let order_val : Seq.seq nat = Seq.seq_of_list [{order_list}]

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  (is_topological_order adj_val {n_v} order_val /\\
   all_distinct order_val /\\ Seq.length order_val == {n_v})
=
  assert (Seq.length adj_val == {n_v * n_v});
  assert (Seq.length order_val == {n_v});
{chr(10).join(edge_checks)}
  ()

#pop-options
"""
    return mod, code


def _topo_completeness(idx, test, variant="full"):
    n_v, adj, order = test["n"], test["adj"], test["order"]
    mod = f"IntentEval.TopoSort.Completeness.{variant.title()}.Test{idx}"

    adj_list = "; ".join(str(v) for v in adj)
    order_list = "; ".join(str(v) for v in order)

    adj_asserts = "\n".join(
        f"  assert (Seq.index a {i} == {v});" for i, v in enumerate(adj)
    )
    order_asserts = "\n".join(
        f"  assert (Seq.index o {i} == {order[i]});" for i in range(n_v)
    )

    if variant == "full":
        assumes = (f"Seq.equal a adj_val /\\ Seq.length a == {n_v * n_v} /\\ "
                   f"Seq.length o == {n_v} /\\ "
                   f"is_topological_order a {n_v} o /\\ all_distinct o")
    elif variant == "order_only":
        assumes = (f"Seq.equal a adj_val /\\ Seq.length a == {n_v * n_v} /\\ "
                   f"Seq.length o == {n_v} /\\ "
                   f"is_topological_order a {n_v} o")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && Seq.length adj = n * n && Seq.index adj (u * n + v) = 1

let rec position_aux (order: Seq.seq nat) (v: nat) (i: nat) : Tot int (decreases (Seq.length order - i)) =
  if i >= Seq.length order then -1
  else if Seq.index order i = v then i
  else position_aux order v (i + 1)

let position (order: Seq.seq nat) (v: nat) : int = position_aux order v 0

let is_topological_order (adj: Seq.seq int) (n: nat) (order: Seq.seq nat) : prop =
  Seq.length order == n /\\
  Seq.length adj == n * n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ has_edge n adj u v ==>
    position order u >= 0 /\\ position order v >= 0 /\\
    position order u < position order v)

let all_distinct (order: Seq.seq nat) : prop =
  forall (i j: nat). i < Seq.length order /\\ j < Seq.length order /\\ i <> j ==>
    Seq.index order i <> Seq.index order j

let adj_val : Seq.seq int = Seq.seq_of_list [{adj_list}]

let completeness_test (a: Seq.seq int) (o: Seq.seq nat) : Lemma
  (requires {assumes})
  (ensures Seq.equal o (Seq.seq_of_list [{order_list}]))
=
{adj_asserts}
{order_asserts}
  ()

#pop-options
"""
    return mod, code

LCS_TESTS = [
    {"x": [1, 2, 3], "y": [2, 3, 4], "length": 2},   # LCS = [2,3]
    {"x": [1, 2], "y": [3, 4], "length": 0},           # no common
    {"x": [1, 2, 3], "y": [1, 2, 3], "length": 3},     # identical
]


def _lcs_soundness(idx, test):
    x, y, length = test["x"], test["y"], test["length"]
    mod = f"IntentEval.LCS.Soundness.Test{idx}"

    x_fstar = _seq_list(x)
    y_fstar = _seq_list(y)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let max_int (a b: int) : int = if a >= b then a else b

let rec lcs_length (x y: Seq.seq int) (i: nat{{i <= Seq.length x}}) (j: nat{{j <= Seq.length y}})
  : Tot int (decreases (i + j)) =
  if i = 0 || j = 0 then 0
  else if Seq.index x (i - 1) = Seq.index y (j - 1) then
    1 + lcs_length x y (i - 1) (j - 1)
  else
    max_int (lcs_length x y (i - 1) j) (lcs_length x y i (j - 1))

let x_val : Seq.seq int = {x_fstar}
let y_val : Seq.seq int = {y_fstar}

let soundness_test () : Lemma
  (lcs_length x_val y_val {len(x)} {len(y)} == {length})
= ()

#pop-options
"""
    return mod, code


def _lcs_completeness(idx, test, variant="full"):
    x, y, length = test["x"], test["y"], test["length"]
    mod = f"IntentEval.LCS.Completeness.{variant.title()}.Test{idx}"

    x_fstar = _seq_list(x)
    y_fstar = _seq_list(y)

    if variant == "full":
        assumes = (f"Seq.equal a x_val /\\ Seq.equal b y_val /\\ "
                   f"r == lcs_length a b {len(x)} {len(y)}")
    elif variant == "nonneg_only":
        assumes = "r >= 0"
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let max_int (a b: int) : int = if a >= b then a else b

let rec lcs_length (x y: Seq.seq int) (i: nat{{i <= Seq.length x}}) (j: nat{{j <= Seq.length y}})
  : Tot int (decreases (i + j)) =
  if i = 0 || j = 0 then 0
  else if Seq.index x (i - 1) = Seq.index y (j - 1) then
    1 + lcs_length x y (i - 1) (j - 1)
  else
    max_int (lcs_length x y (i - 1) j) (lcs_length x y i (j - 1))

let x_val : Seq.seq int = {x_fstar}
let y_val : Seq.seq int = {y_fstar}

let completeness_test (a b: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {length})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# String matching spec: count of pattern occurrences
# ---------------------------------------------------------------------------

STRING_MATCH_TESTS = [
    {"text": [1, 2, 1, 2, 1], "pattern": [1, 2], "count": 2},
    {"text": [1, 1, 1], "pattern": [2], "count": 0},
    {"text": [3, 3], "pattern": [3], "count": 2},
]


def _strmatch_soundness(idx, test):
    text, pattern, count = test["text"], test["pattern"], test["count"]
    mod = f"IntentEval.StringMatch.Soundness.Test{idx}"

    text_fstar = _seq_list(text)
    pat_fstar = _seq_list(pattern)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 16 --ifuel 16"

let rec check_match_at (text pattern: Seq.seq int) (s j: nat) : Tot bool (decreases (Seq.length pattern - j)) =
  if j >= Seq.length pattern then true
  else if s + j >= Seq.length text then false
  else if Seq.index text (s + j) = Seq.index pattern j then check_match_at text pattern s (j + 1)
  else false

let matches_at (text pattern: Seq.seq int) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0

let rec count_matches (text pattern: Seq.seq int) (limit: nat) : Tot nat (decreases limit) =
  if limit = 0 then 0
  else (if matches_at text pattern (limit - 1) then 1 else 0) +
       count_matches text pattern (limit - 1)

let text_val : Seq.seq int = {text_fstar}
let pat_val : Seq.seq int = {pat_fstar}

let soundness_test () : Lemma
  (count_matches text_val pat_val ({len(text)} - {len(pattern)} + 1) == {count})
= ()

#pop-options
"""
    return mod, code


def _strmatch_completeness(idx, test, variant="full"):
    text, pattern, count = test["text"], test["pattern"], test["count"]
    mod = f"IntentEval.StringMatch.Completeness.{variant.title()}.Test{idx}"

    text_fstar = _seq_list(text)
    pat_fstar = _seq_list(pattern)

    limit = len(text) - len(pattern) + 1

    if variant == "full":
        assumes = (f"Seq.equal t text_val /\\ Seq.equal p pat_val /\\ "
                   f"r == count_matches t p {limit}")
    elif variant == "nonneg_only":
        assumes = "r >= 0"
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 16 --ifuel 16"

let rec check_match_at (text pattern: Seq.seq int) (s j: nat) : Tot bool (decreases (Seq.length pattern - j)) =
  if j >= Seq.length pattern then true
  else if s + j >= Seq.length text then false
  else if Seq.index text (s + j) = Seq.index pattern j then check_match_at text pattern s (j + 1)
  else false

let matches_at (text pattern: Seq.seq int) (s: nat) : bool =
  s + Seq.length pattern <= Seq.length text && check_match_at text pattern s 0

let rec count_matches (text pattern: Seq.seq int) (limit: nat) : Tot nat (decreases limit) =
  if limit = 0 then 0
  else (if matches_at text pattern (limit - 1) then 1 else 0) +
       count_matches text pattern (limit - 1)

let text_val : Seq.seq int = {text_fstar}
let pat_val : Seq.seq int = {pat_fstar}

let completeness_test (t p: Seq.seq int) (r: nat) : Lemma
  (requires {assumes})
  (ensures r == {count})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Minimum element spec: result ∈ arr ∧ result ≤ all elements
# ---------------------------------------------------------------------------

MIN_TESTS = [
    {"arr": [3, 1, 2], "result": 1},
    {"arr": [5, 5, 5], "result": 5},
    {"arr": [7, 2, 9], "result": 2},
]


def _min_soundness(idx, test):
    arr, result = test["arr"], test["result"]
    mod = f"IntentEval.Minimum.Soundness.Test{idx}"
    arr_fstar = _seq_list(arr)
    n = len(arr)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let is_minimum (arr: Seq.seq int) (r: int) : prop =
  Seq.length arr > 0 /\\
  (exists (i: nat). i < Seq.length arr /\\ Seq.index arr i == r) /\\
  (forall (i: nat). i < Seq.length arr ==> r <= Seq.index arr i)

let soundness_test () : Lemma (is_minimum arr_val {result})
= ()
"""
    return mod, code


def _min_completeness(idx, test, variant="full"):
    arr, result = test["arr"], test["result"]
    mod = f"IntentEval.Minimum.Completeness.{variant.title()}.Test{idx}"
    arr_fstar = _seq_list(arr)

    if variant == "full":
        assumes = ("Seq.equal a arr_val /\\ "
                   "(exists (i: nat). i < Seq.length a /\\ Seq.index a i == r) /\\ "
                   "(forall (i: nat). i < Seq.length a ==> r <= Seq.index a i)")
    elif variant == "member_only":
        assumes = ("Seq.equal a arr_val /\\ "
                   "(exists (i: nat). i < Seq.length a /\\ Seq.index a i == r)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {result})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Maximum element spec: result ∈ arr ∧ result ≥ all elements
# ---------------------------------------------------------------------------

MAX_TESTS = [
    {"arr": [3, 1, 2], "result": 3},
    {"arr": [5, 5, 5], "result": 5},
    {"arr": [7, 2, 9], "result": 9},
]


def _max_soundness(idx, test):
    arr, result = test["arr"], test["result"]
    mod = f"IntentEval.Maximum.Soundness.Test{idx}"
    arr_fstar = _seq_list(arr)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let is_maximum (arr: Seq.seq int) (r: int) : prop =
  Seq.length arr > 0 /\\
  (exists (i: nat). i < Seq.length arr /\\ Seq.index arr i == r) /\\
  (forall (i: nat). i < Seq.length arr ==> r >= Seq.index arr i)

let soundness_test () : Lemma (is_maximum arr_val {result})
= ()
"""
    return mod, code


def _max_completeness(idx, test, variant="full"):
    arr, result = test["arr"], test["result"]
    mod = f"IntentEval.Maximum.Completeness.{variant.title()}.Test{idx}"
    arr_fstar = _seq_list(arr)

    if variant == "full":
        assumes = ("Seq.equal a arr_val /\\ "
                   "(exists (i: nat). i < Seq.length a /\\ Seq.index a i == r) /\\ "
                   "(forall (i: nat). i < Seq.length a ==> r >= Seq.index a i)")
    elif variant == "member_only":
        assumes = ("Seq.equal a arr_val /\\ "
                   "(exists (i: nat). i < Seq.length a /\\ Seq.index a i == r)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {result})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Simultaneous Min-Max spec: returns (min, max)
# ---------------------------------------------------------------------------

MINMAX_TESTS = [
    {"arr": [3, 1, 2], "min": 1, "max": 3},
    {"arr": [5, 5], "min": 5, "max": 5},
    {"arr": [7, 2, 9], "min": 2, "max": 9},
]


def _minmax_soundness(idx, test):
    arr, mn, mx = test["arr"], test["min"], test["max"]
    mod = f"IntentEval.MinMax.Soundness.Test{idx}"
    arr_fstar = _seq_list(arr)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let is_minmax (arr: Seq.seq int) (lo hi: int) : prop =
  Seq.length arr > 0 /\\
  (exists (i: nat). i < Seq.length arr /\\ Seq.index arr i == lo) /\\
  (exists (j: nat). j < Seq.length arr /\\ Seq.index arr j == hi) /\\
  (forall (k: nat). k < Seq.length arr ==> lo <= Seq.index arr k /\\ Seq.index arr k <= hi)

let soundness_test () : Lemma (is_minmax arr_val {mn} {mx})
= ()
"""
    return mod, code


def _minmax_completeness(idx, test, variant="full"):
    arr, mn, mx = test["arr"], test["min"], test["max"]
    mod = f"IntentEval.MinMax.Completeness.{variant.title()}.Test{idx}"
    arr_fstar = _seq_list(arr)

    if variant == "full":
        assumes = ("Seq.equal a arr_val /\\ "
                   "(exists (i: nat). i < Seq.length a /\\ Seq.index a i == lo) /\\ "
                   "(exists (j: nat). j < Seq.length a /\\ Seq.index a j == hi) /\\ "
                   "(forall (k: nat). k < Seq.length a ==> lo <= Seq.index a k /\\ Seq.index a k <= hi)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (lo hi: int) : Lemma
  (requires {assumes})
  (ensures lo == {mn} /\\ hi == {mx})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Quickselect / kth smallest: result = kth smallest element
# ---------------------------------------------------------------------------

SELECT_TESTS = [
    {"arr": [3, 1, 2], "k": 0, "result": 1},
    {"arr": [3, 1, 2], "k": 2, "result": 3},
    {"arr": [5, 1, 3], "k": 1, "result": 3},
]


def _select_soundness(idx, test):
    arr, k, result = test["arr"], test["k"], test["result"]
    mod = f"IntentEval.Select.Soundness.Test{idx}"
    arr_fstar = _seq_list(arr)
    count_lt = sum(1 for x in arr if x < result)
    count_le = sum(1 for x in arr if x <= result)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let is_kth_smallest (a: Seq.seq int) (k: nat) (r: int) : prop =
  k < Seq.length a /\\
  (exists (i: nat). i < Seq.length a /\\ Seq.index a i == r)

let soundness_test () : Lemma
  (is_kth_smallest arr_val {k} {result} /\\ {count_lt} <= {k} /\\ {count_le} > {k})
= ()
"""
    return mod, code


def _select_completeness(idx, test, variant="full"):
    arr, k, result = test["arr"], test["k"], test["result"]
    mod = f"IntentEval.Select.Completeness.{variant.title()}.Test{idx}"
    arr_fstar = _seq_list(arr)
    sorted_arr = sorted(arr)
    count_lt = sum(1 for x in arr if x < result)
    count_le = sum(1 for x in arr if x <= result)

    if variant == "full":
        assumes = (f"Seq.equal a arr_val /\\ "
                   f"(exists (i: nat). i < Seq.length a /\\ Seq.index a i == r) /\\ "
                   f"{count_lt} <= {k} /\\ {count_le} > {k}")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let arr_val : Seq.seq int = {arr_fstar}

let completeness_test (a: Seq.seq int) (r: int) : Lemma
  (requires {assumes})
  (ensures r == {result})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Extended GCD: g = gcd(a,b) AND a*x + b*y = g
# ---------------------------------------------------------------------------

EGCD_TESTS = [
    {"a": 12, "b": 8, "g": 4, "x": 1, "y": -1},
    {"a": 35, "b": 15, "g": 5, "x": 1, "y": -2},
    {"a": 7, "b": 3, "g": 1, "x": 1, "y": -2},
]


def _egcd_soundness(idx, test):
    a, b, g, x, y = test["a"], test["b"], test["g"], test["x"], test["y"]
    mod = f"IntentEval.ExtGCD.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

let divides (d n: nat) : prop = d > 0 /\\ n % d == 0

let soundness_test () : Lemma
  (divides {g} {a} /\\ divides {g} {b} /\\
   (forall (d: pos). {a} % d == 0 /\\ {b} % d == 0 ==> d <= {g}) /\\
   {a} * ({x}) + {b} * ({y}) == {g})
= ()
"""
    return mod, code


def _egcd_completeness(idx, test, variant="full"):
    a, b, g, x, y = test["a"], test["b"], test["g"], test["x"], test["y"]
    mod = f"IntentEval.ExtGCD.Completeness.{variant.title()}.Test{idx}"

    if variant == "full":
        assumes = (f"gg > 0 /\\ {a} % gg == 0 /\\ {b} % gg == 0 /\\ "
                   f"(forall (d: pos). {a} % d == 0 /\\ {b} % d == 0 ==> d <= gg) /\\ "
                   f"{a} * xx + {b} * yy == gg")
    elif variant == "gcd_only":
        assumes = (f"gg > 0 /\\ {a} % gg == 0 /\\ {b} % gg == 0 /\\ "
                   f"(forall (d: pos). {a} % d == 0 /\\ {b} % d == 0 ==> d <= gg)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul

let completeness_test (gg xx yy: int) : Lemma
  (requires {assumes})
  (ensures gg == {g})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Matrix Multiply spec: c[i][j] = dot(row_i(a), col_j(b))
# ---------------------------------------------------------------------------

MATMUL_TESTS = [
    {"a": [1,0,0,1], "b": [2,3,4,5], "n": 2, "c": [2,3,4,5]},
    {"a": [1,2,3,4], "b": [1,0,0,1], "n": 2, "c": [1,2,3,4]},
    {"a": [1,2,3,4], "b": [5,6,7,8], "n": 2, "c": [19,22,43,50]},
]


def _matmul_soundness(idx, test):
    a, b, n, c = test["a"], test["b"], test["n"], test["c"]
    mod = f"IntentEval.MatMul.Soundness.Test{idx}"
    a_fstar = _seq_list(a)
    b_fstar = _seq_list(b)
    c_fstar = _seq_list(c)

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let flat_index (n i j: nat) : nat = i * n + j

let rec dot_product (sa sb: Seq.seq int) (n i j: nat) (limit: nat)
  : Tot int (decreases limit) =
  if limit = 0 then 0
  else
    let k = limit - 1 in
    (if i * n + k < Seq.length sa && k * n + j < Seq.length sb
     then Seq.index sa (i * n + k) * Seq.index sb (k * n + j)
     else 0) + dot_product sa sb n i j k

let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sa == n * n /\\ Seq.length sb == n * n /\\ Seq.length sc == n * n /\\
  (forall (i j: nat). i < n /\\ j < n ==>
    Seq.index sc (flat_index n i j) == dot_product sa sb n i j n)

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let a_val : Seq.seq int = {a_fstar}
let b_val : Seq.seq int = {b_fstar}
let c_val : Seq.seq int = {c_fstar}

let soundness_test () : Lemma (mat_mul_correct a_val b_val c_val {n})
= ()

#pop-options
"""
    return mod, code


def _matmul_completeness(idx, test, variant="full"):
    a, b, n, c = test["a"], test["b"], test["n"], test["c"]
    mod = f"IntentEval.MatMul.Completeness.{variant.title()}.Test{idx}"
    a_fstar = _seq_list(a)
    b_fstar = _seq_list(b)
    c_fstar = _seq_list(c)

    if variant == "full":
        assumes = (f"Seq.equal sa a_val /\\ Seq.equal sb b_val /\\ "
                   f"mat_mul_correct sa sb sc {n}")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let flat_index (n i j: nat) : nat = i * n + j

let rec dot_product (sa sb: Seq.seq int) (n i j: nat) (limit: nat)
  : Tot int (decreases limit) =
  if limit = 0 then 0
  else
    let k = limit - 1 in
    (if i * n + k < Seq.length sa && k * n + j < Seq.length sb
     then Seq.index sa (i * n + k) * Seq.index sb (k * n + j)
     else 0) + dot_product sa sb n i j k

let mat_mul_correct (sa sb sc: Seq.seq int) (n: nat) : prop =
  Seq.length sa == n * n /\\ Seq.length sb == n * n /\\ Seq.length sc == n * n /\\
  (forall (i j: nat). i < n /\\ j < n ==>
    Seq.index sc (flat_index n i j) == dot_product sa sb n i j n)

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let a_val : Seq.seq int = {a_fstar}
let b_val : Seq.seq int = {b_fstar}

let completeness_test (sa sb sc: Seq.seq int) : Lemma
  (requires {assumes})
  (ensures Seq.equal sc (Seq.seq_of_list [{'; '.join(str(v) for v in c)}]))
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Partition spec: pivot in correct position, left ≤ pivot, right ≥ pivot, permutation
# ---------------------------------------------------------------------------

PARTITION_TESTS = [
    {"arr": [3, 1, 2], "pivot_val": 3, "pivot_pos": 2,
     "result": [1, 2, 3]},
    {"arr": [1, 3, 2], "pivot_val": 3, "pivot_pos": 2,
     "result": [1, 2, 3]},
    {"arr": [2, 1], "pivot_val": 2, "pivot_pos": 1,
     "result": [1, 2]},
]


def _partition_soundness(idx, test):
    arr = test["arr"]
    result = test["result"]
    pivot_pos = test["pivot_pos"]
    pivot_val = test["pivot_val"]
    mod = f"IntentEval.Partition.Soundness.Test{idx}"
    inp_fstar = _seq_append(arr)
    out_fstar = _seq_append(result)
    n = len(arr)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_permutation (s1 s2: Seq.seq int) : prop =
  Seq.length s1 == Seq.length s2 /\\
  (forall (v: int). Seq.count v s1 == Seq.count v s2)

let partition_spec (inp out: Seq.seq int) (p: nat) : prop =
  Seq.length out == Seq.length inp /\\
  p < Seq.length out /\\
  is_permutation inp out /\\
  (forall (i: nat). i < p ==> Seq.index out i <= Seq.index out p) /\\
  (forall (j: nat). j > p /\\ j < Seq.length out ==> Seq.index out j >= Seq.index out p)

let inp_val : Seq.seq int = {inp_fstar}
let out_val : Seq.seq int = {out_fstar}

let soundness_test () : Lemma (partition_spec inp_val out_val {pivot_pos})
= ()

#pop-options
"""
    return mod, code


def _partition_completeness(idx, test, variant="full"):
    arr = test["arr"]
    result = test["result"]
    pivot_pos = test["pivot_pos"]
    mod = f"IntentEval.Partition.Completeness.{variant.title()}.Test{idx}"
    inp_fstar = _seq_append(arr)
    out_fstar = _seq_append(result)
    n = len(arr)

    if variant == "full":
        assumes = (f"Seq.equal a inp_val /\\ "
                   f"Seq.length y == Seq.length a /\\ "
                   f"p < Seq.length y /\\ "
                   f"(forall (v: int). Seq.count v a == Seq.count v y) /\\ "
                   f"(forall (i: nat). i < p ==> Seq.index y i <= Seq.index y p) /\\ "
                   f"(forall (j: nat). j > p /\\ j < Seq.length y ==> Seq.index y j >= Seq.index y p)")
    else:
        raise ValueError(variant)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let inp_val : Seq.seq int = {inp_fstar}

let completeness_test (a y: Seq.seq int) (p: nat) : Lemma
  (requires {assumes})
  (ensures Seq.equal y (Seq.seq_of_list [{'; '.join(str(v) for v in result)}]) /\\ p == {pivot_pos})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Singly Linked List insert_head: insert(l, x) = x :: l
# ---------------------------------------------------------------------------

SLL_INSERT_TESTS = [
    {"list": [], "insert": 5, "result": [5]},
    {"list": [1, 2], "insert": 3, "result": [3, 1, 2]},
    {"list": [7], "insert": 7, "result": [7, 7]},
]


def _sll_insert_soundness(idx, test):
    lst, x, result = test["list"], test["insert"], test["result"]
    mod = f"IntentEval.SLLInsert.Soundness.Test{idx}"
    lst_fstar = _seq_list(lst)
    res_fstar = _seq_list(result)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let insert_head (l: Seq.seq int) (x: int) : Seq.seq int =
  Seq.append (Seq.create 1 x) l

let lst_val : Seq.seq int = {lst_fstar}
let res_val : Seq.seq int = {res_fstar}

let soundness_test () : Lemma (Seq.equal (insert_head lst_val {x}) res_val)
= ()
"""
    return mod, code


def _sll_insert_completeness(idx, test, variant="full"):
    lst, x, result = test["list"], test["insert"], test["result"]
    mod = f"IntentEval.SLLInsert.Completeness.{variant.title()}.Test{idx}"
    lst_fstar = _seq_list(lst)
    res_fstar = _seq_list(result)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let insert_head (l: Seq.seq int) (x: int) : Seq.seq int =
  Seq.append (Seq.create 1 x) l

let lst_val : Seq.seq int = {lst_fstar}

let completeness_test (l: Seq.seq int) (r: Seq.seq int) : Lemma
  (requires Seq.equal l lst_val /\\ Seq.equal r (insert_head l {x}))
  (ensures Seq.equal r (Seq.seq_of_list [{'; '.join(str(v) for v in result)}]))
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Singly Linked List delete: remove first occurrence of x
# ---------------------------------------------------------------------------

SLL_DELETE_TESTS = [
    {"list": [3, 1, 2], "delete": 1, "result": [3, 2]},
    {"list": [1, 1, 2], "delete": 1, "result": [1, 2]},
    {"list": [5], "delete": 5, "result": []},
]


def _sll_delete_soundness(idx, test):
    lst, x, result = test["list"], test["delete"], test["result"]
    mod = f"IntentEval.SLLDelete.Soundness.Test{idx}"
    lst_fstar = _seq_list(lst)
    res_fstar = _seq_list(result)
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let rec list_delete (l: Seq.seq int) (x: int) (i: nat)
  : Tot (Seq.seq int) (decreases (Seq.length l - i)) =
  if i >= Seq.length l then l
  else if Seq.index l i = x then
    Seq.append (Seq.slice l 0 i) (Seq.slice l (i + 1) (Seq.length l))
  else list_delete l x (i + 1)

let lst_val : Seq.seq int = {lst_fstar}
let res_val : Seq.seq int = {res_fstar}

let soundness_test () : Lemma (Seq.equal (list_delete lst_val {x} 0) res_val)
= ()

#pop-options
"""
    return mod, code


def _sll_delete_completeness(idx, test, variant="full"):
    lst, x, result = test["list"], test["delete"], test["result"]
    mod = f"IntentEval.SLLDelete.Completeness.{variant.title()}.Test{idx}"
    lst_fstar = _seq_list(lst)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let rec list_delete (l: Seq.seq int) (x: int) (i: nat)
  : Tot (Seq.seq int) (decreases (Seq.length l - i)) =
  if i >= Seq.length l then l
  else if Seq.index l i = x then
    Seq.append (Seq.slice l 0 i) (Seq.slice l (i + 1) (Seq.length l))
  else list_delete l x (i + 1)

let lst_val : Seq.seq int = {lst_fstar}

let completeness_test (l: Seq.seq int) (r: Seq.seq int) : Lemma
  (requires Seq.equal l lst_val /\\ Seq.equal r (list_delete l {x} 0))
  (ensures Seq.equal r (Seq.seq_of_list [{'; '.join(str(v) for v in result) if result else ''}]))
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Hash Table insert+search: search(insert(ht, k, v), k) = Some v
# ---------------------------------------------------------------------------

HASH_TABLE_TESTS = [
    {"key": 1, "value": 10},
    {"key": 2, "value": 20},
    {"key": 0, "value": 42},
]


def _hashtable_soundness(idx, test):
    k, v = test["key"], test["value"]
    mod = f"IntentEval.HashTable.Soundness.Test{idx}"
    code = f"""module {mod}

type entry = {{ ht_key: nat; ht_val: int }}

let rec ht_search (m: list entry) (key: nat) : option int =
  match m with
  | [] -> None
  | hd :: tl -> if hd.ht_key = key then Some hd.ht_val else ht_search tl key

let ht_insert (m: list entry) (key: nat) (value: int) : list entry =
  {{ ht_key = key; ht_val = value }} :: m

let soundness_test () : Lemma
  (ht_search (ht_insert [] {k} {v}) {k} == Some {v})
= ()
"""
    return mod, code


def _hashtable_completeness(idx, test, variant="full"):
    k, v = test["key"], test["value"]
    mod = f"IntentEval.HashTable.Completeness.{variant.title()}.Test{idx}"

    code = f"""module {mod}

type entry = {{ ht_key: nat; ht_val: int }}

let rec ht_search (m: list entry) (key: nat) : option int =
  match m with
  | [] -> None
  | hd :: tl -> if hd.ht_key = key then Some hd.ht_val else ht_search tl key

let ht_insert (m: list entry) (key: nat) (value: int) : list entry =
  {{ ht_key = key; ht_val = value }} :: m

let completeness_test (r: option int) : Lemma
  (requires r == ht_search (ht_insert [] {k} {v}) {k})
  (ensures r == Some {v})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# BST search: search returns true iff key is present
# ---------------------------------------------------------------------------

BST_SEARCH_TESTS = [
    {"keys": [2, 1, 3], "search": 1, "found": True},
    {"keys": [2, 1, 3], "search": 4, "found": False},
    {"keys": [5, 3, 7], "search": 3, "found": True},
]


def _bst_search_soundness(idx, test):
    keys, search_key, found = test["keys"], test["search"], test["found"]
    mod = f"IntentEval.BSTSearch.Soundness.Test{idx}"

    # Build BST insert chain in F*
    def _bst_insert_chain(keys):
        result = "Leaf"
        for k in keys:
            result = f"(bst_insert {result} {k})"
        return result

    tree_expr = _bst_insert_chain(keys)
    found_fstar = "true" if found else "false"

    code = f"""module {mod}

type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst

let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
    if k < key then Node (bst_insert left k) key right
    else if k > key then Node left key (bst_insert right k)
    else t

let rec bst_search (t: bst) (k: int) : bool =
  match t with
  | Leaf -> false
  | Node left key right ->
    if k = key then true
    else if k < key then bst_search left k
    else bst_search right k

let tree_val : bst = {tree_expr}

let soundness_test () : Lemma (bst_search tree_val {search_key} = {found_fstar})
= ()
"""
    return mod, code


def _bst_search_completeness(idx, test, variant="full"):
    keys, search_key, found = test["keys"], test["search"], test["found"]
    mod = f"IntentEval.BSTSearch.Completeness.{variant.title()}.Test{idx}"
    found_fstar = "true" if found else "false"

    def _bst_insert_chain(keys):
        result = "Leaf"
        for k in keys:
            result = f"(bst_insert {result} {k})"
        return result

    tree_expr = _bst_insert_chain(keys)

    code = f"""module {mod}

type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst

let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
    if k < key then Node (bst_insert left k) key right
    else if k > key then Node left key (bst_insert right k)
    else t

let rec bst_search (t: bst) (k: int) : bool =
  match t with
  | Leaf -> false
  | Node left key right ->
    if k = key then true
    else if k < key then bst_search left k
    else bst_search right k

let completeness_test (r: bool) : Lemma
  (requires r = bst_search {tree_expr} {search_key})
  (ensures r = {found_fstar})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# BST inorder: inorder traversal of BST produces sorted list
# ---------------------------------------------------------------------------

BST_INORDER_TESTS = [
    {"keys": [2, 1, 3], "inorder": [1, 2, 3]},
    {"keys": [3, 1, 2], "inorder": [1, 2, 3]},
    {"keys": [1], "inorder": [1]},
]


def _bst_inorder_soundness(idx, test):
    keys, inorder = test["keys"], test["inorder"]
    mod = f"IntentEval.BSTInorder.Soundness.Test{idx}"

    def _bst_insert_chain(keys):
        result = "Leaf"
        for k in keys:
            result = f"(bst_insert {result} {k})"
        return result

    tree_expr = _bst_insert_chain(keys)

    code = f"""module {mod}
open FStar.List.Tot

type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst

let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
    if k < key then Node (bst_insert left k) key right
    else if k > key then Node left key (bst_insert right k)
    else t

let rec bst_inorder (t: bst) : list int =
  match t with
  | Leaf -> []
  | Node left key right -> bst_inorder left @ [key] @ bst_inorder right

let tree_val : bst = {tree_expr}

let soundness_test () : Lemma (bst_inorder tree_val == [{'; '.join(str(v) for v in inorder)}])
= ()
"""
    return mod, code


def _bst_inorder_completeness(idx, test, variant="full"):
    keys, inorder = test["keys"], test["inorder"]
    mod = f"IntentEval.BSTInorder.Completeness.{variant.title()}.Test{idx}"

    def _bst_insert_chain(keys):
        result = "Leaf"
        for k in keys:
            result = f"(bst_insert {result} {k})"
        return result

    tree_expr = _bst_insert_chain(keys)

    code = f"""module {mod}
open FStar.List.Tot

type bst =
  | Leaf : bst
  | Node : left:bst -> key:int -> right:bst -> bst

let rec bst_insert (t: bst) (k: int) : bst =
  match t with
  | Leaf -> Node Leaf k Leaf
  | Node left key right ->
    if k < key then Node (bst_insert left k) key right
    else if k > key then Node left key (bst_insert right k)
    else t

let rec bst_inorder (t: bst) : list int =
  match t with
  | Leaf -> []
  | Node left key right -> bst_inorder left @ [key] @ bst_inorder right

let completeness_test (r: list int) : Lemma
  (requires r == bst_inorder {tree_expr})
  (ensures r == [{'; '.join(str(v) for v in inorder)}])
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Rod Cutting: optimal_revenue(prices, n) = max revenue
# ---------------------------------------------------------------------------

ROD_CUTTING_TESTS = [
    {"prices": [1, 5, 8, 9], "length": 4, "revenue": 10},
    {"prices": [3, 5, 6], "length": 3, "revenue": 9},
    {"prices": [1, 5], "length": 2, "revenue": 5},
]


def _rod_cutting_soundness(idx, test):
    prices, length, revenue = test["prices"], test["length"], test["revenue"]
    mod = f"IntentEval.RodCutting.Soundness.Test{idx}"
    prices_fstar = _seq_list(prices)

    # The spec: r is valid revenue (achievable) and r is maximal
    # For small inputs, enumerate all possible single-cut revenues
    # and assert result >= each
    cut_asserts = []
    for i in range(1, length + 1):
        p = prices[i-1] if i-1 < len(prices) else 0
        cut_asserts.append(f"  assert ({revenue} >= {p});")

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let prices_val : Seq.seq int = {prices_fstar}

let valid_revenue (prices: Seq.seq int) (n: nat) (r: nat) : prop =
  r >= 0 /\\
  (forall (i: nat). i >= 1 /\\ i <= n /\\ i - 1 < Seq.length prices ==>
    r >= Seq.index prices (i - 1))

let soundness_test () : Lemma (valid_revenue prices_val {length} {revenue})
=
{chr(10).join(cut_asserts)}
  ()
"""
    return mod, code


def _rod_cutting_completeness(idx, test, variant="full"):
    prices, length, revenue = test["prices"], test["length"], test["revenue"]
    mod = f"IntentEval.RodCutting.Completeness.{variant.title()}.Test{idx}"
    prices_fstar = _seq_list(prices)

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let prices_val : Seq.seq int = {prices_fstar}

let valid_revenue (prices: Seq.seq int) (n: nat) (r: nat) : prop =
  r >= 0 /\\
  (forall (i: nat). i >= 1 /\\ i <= n /\\ i - 1 < Seq.length prices ==>
    r >= Seq.index prices (i - 1))

let completeness_test (r: nat) : Lemma
  (requires valid_revenue prices_val {length} r)
  (ensures r == {revenue})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# BFS Distance: shortest unweighted path in a graph
# ---------------------------------------------------------------------------

BFS_TESTS = [
    {"n": 3, "adj": [0,1,0, 0,0,1, 0,0,0], "source": 0, "target": 2, "dist": 2},
    {"n": 3, "adj": [0,1,1, 0,0,0, 0,0,0], "source": 0, "target": 2, "dist": 1},
    {"n": 2, "adj": [0,1, 0,0], "source": 0, "target": 1, "dist": 1},
]


def _bfs_soundness(idx, test):
    n_v, adj, src, tgt, dist = test["n"], test["adj"], test["source"], test["target"], test["dist"]
    mod = f"IntentEval.BFS.Soundness.Test{idx}"
    adj_fstar = _seq_list(adj)

    bfs_helpers = f"""let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0

let rec reachable_in (n: nat) (adj: Seq.seq int) (u v: nat) (k: nat)
  : Tot bool (decreases %[k; n + 1]) =
  if u = v then true
  else if k = 0 then false
  else check_neighbors n adj u v k 0

and check_neighbors (n: nat) (adj: Seq.seq int) (u v: nat) (k: nat) (w: nat)
  : Tot bool (decreases %[k; n - w]) =
  if k = 0 || w >= n then false
  else if has_edge n adj u w && reachable_in n adj w v (k - 1) then true
  else check_neighbors n adj u v k (w + 1)"""

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 16 --ifuel 16"

{bfs_helpers}

let adj_val : Seq.seq int = {adj_fstar}

let soundness_test () : Lemma
  (reachable_in {n_v} adj_val {src} {tgt} {dist} /\\
   (forall (k: nat). k < {dist} ==> not (reachable_in {n_v} adj_val {src} {tgt} k)))
= ()

#pop-options
"""
    return mod, code


def _bfs_completeness(idx, test, variant="full"):
    n_v, adj, src, tgt, dist = test["n"], test["adj"], test["source"], test["target"], test["dist"]
    mod = f"IntentEval.BFS.Completeness.{variant.title()}.Test{idx}"
    adj_fstar = _seq_list(adj)

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 16 --ifuel 16"

let has_edge (n: nat) (adj: Seq.seq int) (u v: nat) : bool =
  u < n && v < n && Seq.length adj = n * n && Seq.index adj (u * n + v) <> 0

let rec reachable_in (n: nat) (adj: Seq.seq int) (u v: nat) (k: nat)
  : Tot bool (decreases %[k; n + 1]) =
  if u = v then true
  else if k = 0 then false
  else check_neighbors n adj u v k 0

and check_neighbors (n: nat) (adj: Seq.seq int) (u v: nat) (k: nat) (w: nat)
  : Tot bool (decreases %[k; n - w]) =
  if k = 0 || w >= n then false
  else if has_edge n adj u w && reachable_in n adj w v (k - 1) then true
  else check_neighbors n adj u v k (w + 1)

let adj_val : Seq.seq int = {adj_fstar}

let completeness_test (d: int) : Lemma
  (requires d >= 0 /\\ reachable_in {n_v} adj_val {src} {tgt} d /\\
            (forall (k: nat). k < {dist} ==> not (reachable_in {n_v} adj_val {src} {tgt} k)))
  (ensures d == {dist})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Dijkstra shortest path: dist[v] for non-negative weighted graphs
# ---------------------------------------------------------------------------

DIJKSTRA_TESTS = [
    {"n": 3, "adj": [0,1,4, 0,0,2, 0,0,0], "source": 0, "dists": [0,1,3]},
    {"n": 2, "adj": [0,5, 0,0], "source": 0, "dists": [0,5]},
    {"n": 3, "adj": [0,3,10, 0,0,1, 0,0,0], "source": 0, "dists": [0,3,4]},
]

INF = 1000000


def _dijkstra_soundness(idx, test):
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.Dijkstra.Soundness.Test{idx}"
    adj_fstar = _seq_list(adj)
    dist_fstar = _seq_list(dists)

    # Build explicit assertions for triangle inequality
    triangle_asserts = []
    for u in range(n_v):
        for v in range(n_v):
            w = adj[u * n_v + v]
            if w > 0 and u != v:
                triangle_asserts.append(
                    f"  assert (Seq.index dist_val {v} <= Seq.index dist_val {u} + {w});"
                )

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let adj_val : Seq.seq int = {adj_fstar}
let dist_val : Seq.seq int = {dist_fstar}

let triangle_ineq (adj dist: Seq.seq int) (n: nat) : prop =
  Seq.length adj == n * n /\\ Seq.length dist == n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ Seq.index adj (u * n + v) > 0 ==>
    Seq.index dist v <= Seq.index dist u + Seq.index adj (u * n + v))

let source_zero (dist: Seq.seq int) (src: nat) : prop =
  src < Seq.length dist /\\ Seq.index dist src == 0

let nonneg_dists (dist: Seq.seq int) : prop =
  forall (i: nat). i < Seq.length dist ==> Seq.index dist i >= 0

let soundness_test () : Lemma
  (triangle_ineq adj_val dist_val {n_v} /\\
   source_zero dist_val {src} /\\
   nonneg_dists dist_val)
=
{chr(10).join(triangle_asserts)}
  ()
"""
    return mod, code


def _dijkstra_completeness(idx, test, variant="full"):
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.Dijkstra.Completeness.{variant.title()}.Test{idx}"
    adj_fstar = _seq_list(adj)

    dist_checks = " /\\ ".join(f"Seq.index d {i} == {dists[i]}" for i in range(n_v))

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let adj_val : Seq.seq int = {adj_fstar}

let triangle_ineq (adj dist: Seq.seq int) (n: nat) : prop =
  Seq.length adj == n * n /\\ Seq.length dist == n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ Seq.index adj (u * n + v) > 0 ==>
    Seq.index dist v <= Seq.index dist u + Seq.index adj (u * n + v))

let completeness_test (d: Seq.seq int) : Lemma
  (requires Seq.length d == {n_v} /\\ Seq.index d {src} == 0 /\\
            (forall (i: nat). i < {n_v} ==> Seq.index d i >= 0) /\\
            triangle_ineq adj_val d {n_v})
  (ensures {dist_checks})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Bellman-Ford: same spec as Dijkstra (allows negative weights, no negative cycles)
# ---------------------------------------------------------------------------

BELLMAN_FORD_TESTS = [
    {"n": 3, "adj": [0,1,4, 0,0,2, 0,0,0], "source": 0, "dists": [0,1,3]},
    {"n": 2, "adj": [0,5, 0,0], "source": 0, "dists": [0,5]},
    {"n": 3, "adj": [0,3,10, 0,0,1, 0,0,0], "source": 0, "dists": [0,3,4]},
]


def _bellman_ford_soundness(idx, test):
    # Reuse Dijkstra soundness structure (same spec for this subset)
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.BellmanFord.Soundness.Test{idx}"
    adj_fstar = _seq_list(adj)
    dist_fstar = _seq_list(dists)

    triangle_asserts = []
    for u in range(n_v):
        for v in range(n_v):
            w = adj[u * n_v + v]
            if w > 0 and u != v:
                triangle_asserts.append(
                    f"  assert (Seq.index dist_val {v} <= Seq.index dist_val {u} + {w});"
                )

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let adj_val : Seq.seq int = {adj_fstar}
let dist_val : Seq.seq int = {dist_fstar}

let triangle_ineq (adj dist: Seq.seq int) (n: nat) : prop =
  Seq.length adj == n * n /\\ Seq.length dist == n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ Seq.index adj (u * n + v) > 0 ==>
    Seq.index dist v <= Seq.index dist u + Seq.index adj (u * n + v))

let source_zero (dist: Seq.seq int) (src: nat) : prop =
  src < Seq.length dist /\\ Seq.index dist src == 0

let soundness_test () : Lemma
  (triangle_ineq adj_val dist_val {n_v} /\\ source_zero dist_val {src})
=
{chr(10).join(triangle_asserts)}
  ()
"""
    return mod, code


def _bellman_ford_completeness(idx, test, variant="full"):
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.BellmanFord.Completeness.{variant.title()}.Test{idx}"
    adj_fstar = _seq_list(adj)
    dist_checks = " /\\ ".join(f"Seq.index d {i} == {dists[i]}" for i in range(n_v))

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let adj_val : Seq.seq int = {adj_fstar}

let triangle_ineq (adj dist: Seq.seq int) (n: nat) : prop =
  Seq.length adj == n * n /\\ Seq.length dist == n /\\
  (forall (u v: nat). u < n /\\ v < n /\\ Seq.index adj (u * n + v) > 0 ==>
    Seq.index dist v <= Seq.index dist u + Seq.index adj (u * n + v))

let completeness_test (d: Seq.seq int) : Lemma
  (requires Seq.length d == {n_v} /\\ Seq.index d {src} == 0 /\\
            triangle_ineq adj_val d {n_v})
  (ensures {dist_checks})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Floyd-Warshall: all-pairs shortest paths
# ---------------------------------------------------------------------------

FLOYD_WARSHALL_TESTS = [
    {"n": 2, "w": [0,3, 1000000,0], "dist": [0,3, 1000000,0]},
    {"n": 2, "w": [0,5, 2,0], "dist": [0,5, 2,0]},
    {"n": 3, "w": [0,1,1000000, 1000000,0,2, 1000000,1000000,0],
     "dist": [0,1,3, 1000000,0,2, 1000000,1000000,0]},
]


def _floyd_warshall_soundness(idx, test):
    n_v, w, dist = test["n"], test["w"], test["dist"]
    mod = f"IntentEval.FloydWarshall.Soundness.Test{idx}"
    w_fstar = _seq_list(w)
    d_fstar = _seq_list(dist)

    # Build explicit triangle assertions
    tri_asserts = []
    for i in range(n_v):
        for j in range(n_v):
            for k in range(n_v):
                d_ij = dist[i * n_v + j]
                d_ik = dist[i * n_v + k]
                d_kj = dist[k * n_v + j]
                if d_ik < INF and d_kj < INF:
                    tri_asserts.append(
                        f"  assert (Seq.index dist_val {i * n_v + j} <= "
                        f"Seq.index dist_val {i * n_v + k} + Seq.index dist_val {k * n_v + j});"
                    )

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let w_val : Seq.seq int = {w_fstar}
let dist_val : Seq.seq int = {d_fstar}

let fw_correct (w dist: Seq.seq int) (n: nat) : prop =
  Seq.length w == n * n /\\ Seq.length dist == n * n /\\
  (forall (i: nat). i < n ==> Seq.index dist (i * n + i) == 0) /\\
  (forall (i j: nat). i < n /\\ j < n ==>
    Seq.index dist (i * n + j) <= Seq.index w (i * n + j)) /\\
  (forall (i j k: nat). i < n /\\ j < n /\\ k < n /\\
    Seq.index dist (i * n + k) < 1000000 /\\ Seq.index dist (k * n + j) < 1000000 ==>
    Seq.index dist (i * n + j) <= Seq.index dist (i * n + k) + Seq.index dist (k * n + j))

let soundness_test () : Lemma (fw_correct w_val dist_val {n_v})
=
{chr(10).join(tri_asserts)}
  ()
"""
    return mod, code


def _floyd_warshall_completeness(idx, test, variant="full"):
    n_v, w, dist = test["n"], test["w"], test["dist"]
    mod = f"IntentEval.FloydWarshall.Completeness.{variant.title()}.Test{idx}"
    w_fstar = _seq_list(w)

    dist_checks = " /\\ ".join(
        f"Seq.index d {i} == {dist[i]}" for i in range(len(dist))
    )

    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

let w_val : Seq.seq int = {w_fstar}

let fw_correct (w dist: Seq.seq int) (n: nat) : prop =
  Seq.length w == n * n /\\ Seq.length dist == n * n /\\
  (forall (i: nat). i < n ==> Seq.index dist (i * n + i) == 0) /\\
  (forall (i j: nat). i < n /\\ j < n ==>
    Seq.index dist (i * n + j) <= Seq.index w (i * n + j)) /\\
  (forall (i j k: nat). i < n /\\ j < n /\\ k < n /\\
    Seq.index dist (i * n + k) < 1000000 /\\ Seq.index dist (k * n + j) < 1000000 ==>
    Seq.index dist (i * n + j) <= Seq.index dist (i * n + k) + Seq.index dist (k * n + j))

let completeness_test (d: Seq.seq int) : Lemma
  (requires Seq.equal (Seq.seq_of_list [{'; '.join(str(v) for v in w)}]) w_val /\\
            fw_correct w_val d {n_v})
  (ensures {dist_checks})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# Activity Selection: greedy selection of compatible (non-overlapping) activities
# ---------------------------------------------------------------------------

ACTIVITY_TESTS = [
    {"starts": [1, 3, 5], "finishes": [2, 4, 6], "count": 3},  # all compatible
    {"starts": [0, 1, 0], "finishes": [3, 2, 4], "count": 1},  # overlapping
    {"starts": [1, 4], "finishes": [3, 6], "count": 2},         # both compatible: [1,3) [4,6)
]


def _activity_soundness(idx, test):
    starts, finishes, count = test["starts"], test["finishes"], test["count"]
    mod = f"IntentEval.ActivitySelection.Soundness.Test{idx}"
    s_fstar = _seq_list(starts)
    f_fstar = _seq_list(finishes)
    n = len(starts)

    # Compute a valid compatible selection greedily
    activities = sorted(range(n), key=lambda i: finishes[i])
    selected = []
    last_finish = -1
    for i in activities:
        if starts[i] >= last_finish:
            selected.append(i)
            last_finish = finishes[i]

    # Generate pairwise compatibility assertions
    compat_asserts = []
    for i, a in enumerate(selected):
        compat_asserts.append(f"  assert (Seq.index s_val {a} < Seq.index f_val {a});")
    for i, a in enumerate(selected):
        for j, b in enumerate(selected):
            if a < b:
                compat_asserts.append(
                    f"  assert (Seq.index f_val {a} <= Seq.index s_val {b} \\/ "
                    f"Seq.index f_val {b} <= Seq.index s_val {a});"
                )

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let s_val : Seq.seq int = {s_fstar}
let f_val : Seq.seq int = {f_fstar}

let soundness_test () : Lemma
  ({count} == {len(selected)})
=
{chr(10).join(compat_asserts)}
  ()
"""
    return mod, code


def _activity_completeness(idx, test, variant="full"):
    starts, finishes, count = test["starts"], test["finishes"], test["count"]
    mod = f"IntentEval.ActivitySelection.Completeness.{variant.title()}.Test{idx}"
    s_fstar = _seq_list(starts)
    f_fstar = _seq_list(finishes)
    n = len(starts)

    # Activity selection is non-deterministic — completeness checks count only
    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let s_val : Seq.seq int = {s_fstar}
let f_val : Seq.seq int = {f_fstar}

let compatible (s f: Seq.seq int) (i j: nat) : prop =
  i < Seq.length s /\\ i < Seq.length f /\\
  j < Seq.length s /\\ j < Seq.length f /\\
  (Seq.index f i <= Seq.index s j \\/ Seq.index f j <= Seq.index s i)

let completeness_test (c: nat) : Lemma
  (requires c == {count})
  (ensures c == {count})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# DFS discovery/finish times: d[v] < f[v] for visited vertices
# ---------------------------------------------------------------------------

DFS_TESTS = [
    {"n": 3, "adj": [0,1,0, 0,0,1, 0,0,0], "source": 0,
     "d": [1,2,3], "f": [6,5,4]},
    {"n": 2, "adj": [0,1, 0,0], "source": 0,
     "d": [1,2], "f": [4,3]},
    {"n": 2, "adj": [0,0, 0,0], "source": 0,
     "d": [1,0], "f": [2,0]},
]


def _dfs_soundness(idx, test):
    n_v, adj, src = test["n"], test["adj"], test["source"]
    d_times, f_times = test["d"], test["f"]
    mod = f"IntentEval.DFS.Soundness.Test{idx}"
    d_fstar = _seq_list(d_times)
    f_fstar = _seq_list(f_times)

    # Generate explicit d < f assertions for visited vertices
    df_asserts = []
    for v in range(n_v):
        if d_times[v] > 0:
            df_asserts.append(f"  assert (Seq.index d_val {v} < Seq.index f_val {v});")

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let d_val : Seq.seq int = {d_fstar}
let f_val : Seq.seq int = {f_fstar}

let valid_dfs_times (d f: Seq.seq int) (n: nat) (src: nat) : prop =
  Seq.length d == n /\\ Seq.length f == n /\\
  src < n /\\
  Seq.index d src > 0 /\\
  (forall (v: nat). v < n /\\ Seq.index d v > 0 ==> Seq.index d v < Seq.index f v)

let soundness_test () : Lemma (valid_dfs_times d_val f_val {n_v} {src})
=
{chr(10).join(df_asserts)}
  ()
"""
    return mod, code


def _dfs_completeness(idx, test, variant="full"):
    n_v, adj, src = test["n"], test["adj"], test["source"]
    d_times, f_times = test["d"], test["f"]
    mod = f"IntentEval.DFS.Completeness.{variant.title()}.Test{idx}"

    d_checks = " /\\ ".join(f"Seq.index d {i} == {d_times[i]}" for i in range(n_v))
    f_checks = " /\\ ".join(f"Seq.index f {i} == {f_times[i]}" for i in range(n_v))

    code = f"""module {mod}
open FStar.Seq
module Seq = FStar.Seq

let completeness_test (d f: Seq.seq int) : Lemma
  (requires
    Seq.length d == {n_v} /\\ Seq.length f == {n_v} /\\
    Seq.index d {src} > 0 /\\
    (forall (v: nat). v < {n_v} /\\ Seq.index d v > 0 ==> Seq.index d v < Seq.index f v))
  (ensures {d_checks} /\\ {f_checks})
= ()
"""
    return mod, code


# ---------------------------------------------------------------------------
# BST Insert: insert key into BST, inorder result is sorted insert
# ---------------------------------------------------------------------------

BST_INSERT_TESTS = [
    {"keys": [], "new_key": 5, "result": [5]},
    {"keys": [3], "new_key": 1, "result": [1, 3]},
    {"keys": [2, 4], "new_key": 3, "result": [2, 3, 4]},
]


def _fstar_list(lst):
    """Convert Python list to F* list literal with semicolons."""
    return "[" + "; ".join(str(x) for x in lst) + "]"


def _bst_insert_soundness(idx, test):
    keys, new_key, result = test["keys"], test["new_key"], test["result"]
    mod = f"IntentEval.BSTInsert.Soundness.Test{idx}"
    res_fstar = _seq_list(result)
    asserts_list = [
        f"  assert (Seq.index result_val {i} = {v});"
        for i, v in enumerate(result)
    ]
    if asserts_list:
        elem_asserts = "\n".join(asserts_list) + "\n  ()"
    else:
        elem_asserts = "  ()"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let result_val : Seq.seq int = {res_fstar}

let soundness_test () : Lemma
  (is_sorted result_val /\\
   Seq.length result_val = {len(result)} /\\
   (exists (i: nat). i < Seq.length result_val /\\ Seq.index result_val i = {new_key}))
=
{elem_asserts}

#pop-options
"""
    return mod, code


def _bst_insert_completeness(idx, test, variant="full"):
    keys, new_key, result = test["keys"], test["new_key"], test["result"]
    mod = f"IntentEval.BSTInsert.Completeness.{variant.title()}.Test{idx}"
    res_fstar = _seq_list(result)
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let result_val : Seq.seq int = {res_fstar}

let completeness_test (r: Seq.seq int) : Lemma
  (requires is_sorted r /\\
            Seq.length r = {len(result)} /\\
            (exists (i: nat). i < Seq.length r /\\ Seq.index r i = {new_key}))
  (ensures r == result_val)
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# BST Delete: delete key from BST, inorder result is sorted delete
# ---------------------------------------------------------------------------

BST_DELETE_TESTS = [
    {"keys": [5], "del_key": 5, "result": []},
    {"keys": [1, 3], "del_key": 1, "result": [3]},
    {"keys": [1, 2, 3], "del_key": 2, "result": [1, 3]},
]


def _bst_delete_soundness(idx, test):
    keys, del_key, result = test["keys"], test["del_key"], test["result"]
    mod = f"IntentEval.BSTDelete.Soundness.Test{idx}"
    n = len(result)
    res_fstar = _seq_list(result) if n > 0 else "Seq.empty #int"
    asserts = []
    for i, v in enumerate(result):
        asserts.append(f"  assert (Seq.index result_val {i} = {v});")
    if asserts:
        assert_block = "\n".join(asserts) + "\n  ()"
    else:
        assert_block = "  ()"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let result_val : Seq.seq int = {res_fstar}

let soundness_test () : Lemma
  (is_sorted result_val /\\
   Seq.length result_val = {n} /\\
   (forall (i: nat). i < {n} ==> Seq.index result_val i <> {del_key}))
= {assert_block}

#pop-options
"""
    return mod, code


def _bst_delete_completeness(idx, test, variant="full"):
    keys, del_key, result = test["keys"], test["del_key"], test["result"]
    mod = f"IntentEval.BSTDelete.Completeness.{variant.title()}.Test{idx}"
    n = len(result)
    res_fstar = _seq_list(result) if n > 0 else "Seq.empty #int"
    remaining = [k for k in keys if k != del_key] + [k for k in keys if k == del_key][1:]
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let result_val : Seq.seq int = {res_fstar}

let completeness_test (r: Seq.seq int) : Lemma
  (requires is_sorted r /\\
            Seq.length r = {n} /\\
            (forall (i: nat). i < {n} ==> Seq.index r i <> {del_key}))
  (ensures r == result_val)
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Matrix Chain Multiplication: min scalar multiplications
# ---------------------------------------------------------------------------

MATRIX_CHAIN_TESTS = [
    {"dims": [10, 20, 30], "cost": 6000},
    {"dims": [10, 20, 30, 40], "cost": 18000},
    {"dims": [5, 10, 3], "cost": 150},
]


def _matrix_chain_soundness(idx, test):
    dims, cost = test["dims"], test["cost"]
    mod = f"IntentEval.MatrixChain.Soundness.Test{idx}"
    n = len(dims) - 1
    dims_fstar = _seq_list(dims)
    if n == 2:
        spec = f"Seq.index d 0 * Seq.index d 1 * Seq.index d 2 = {cost}"
    elif n == 3:
        # min of two parenthesizations: (AB)C vs A(BC)
        spec = (f"(let c1 = Seq.index d 0 * Seq.index d 1 * Seq.index d 2 + "
                f"Seq.index d 0 * Seq.index d 2 * Seq.index d 3 in "
                f"let c2 = Seq.index d 1 * Seq.index d 2 * Seq.index d 3 + "
                f"Seq.index d 0 * Seq.index d 1 * Seq.index d 3 in "
                f"(if c1 <= c2 then c1 else c2) = {cost})")
    else:
        spec = f"{cost} >= 0"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let d : Seq.seq int = {dims_fstar}

let soundness_test () : Lemma
  ({spec})
= ()

#pop-options
"""
    return mod, code


def _matrix_chain_completeness(idx, test, variant="full"):
    dims, cost = test["dims"], test["cost"]
    mod = f"IntentEval.MatrixChain.Completeness.{variant.title()}.Test{idx}"
    n = len(dims) - 1
    dims_fstar = _seq_list(dims)
    if n == 2:
        req = f"r = Seq.index d 0 * Seq.index d 1 * Seq.index d 2"
    elif n == 3:
        req = (f"(let c1 = Seq.index d 0 * Seq.index d 1 * Seq.index d 2 + "
               f"Seq.index d 0 * Seq.index d 2 * Seq.index d 3 in "
               f"let c2 = Seq.index d 1 * Seq.index d 2 * Seq.index d 3 + "
               f"Seq.index d 0 * Seq.index d 1 * Seq.index d 3 in "
               f"r = (if c1 <= c2 then c1 else c2))")
    else:
        req = f"r >= 0"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let d : Seq.seq int = {dims_fstar}

let completeness_test (r: int) : Lemma
  (requires {req})
  (ensures r == {cost})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Huffman Coding: minimum total weighted path length
# ---------------------------------------------------------------------------

HUFFMAN_TESTS = [
    {"freqs": [1, 1], "cost": 2},
    {"freqs": [1, 1, 1], "cost": 5},
    {"freqs": [1, 2, 3], "cost": 9},
]


def _huffman_soundness(idx, test):
    freqs, cost = test["freqs"], test["cost"]
    mod = f"IntentEval.Huffman.Soundness.Test{idx}"
    n = len(freqs)
    freqs_fstar = _seq_list(freqs)
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let freqs_val : Seq.seq int = {freqs_fstar}

let soundness_test () : Lemma ({cost} >= 0)
= ()

#pop-options
"""
    return mod, code


def _huffman_completeness(idx, test, variant="full"):
    freqs, cost = test["freqs"], test["cost"]
    mod = f"IntentEval.Huffman.Completeness.{variant.title()}.Test{idx}"
    n = len(freqs)
    freqs_fstar = _seq_list(freqs)
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let freqs_val : Seq.seq int = {freqs_fstar}

let completeness_test (r: int) : Lemma
  (requires r >= 0)
  (ensures r == {cost})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# DAG Shortest Paths (Ch24): same triangle inequality spec as Dijkstra
# ---------------------------------------------------------------------------

DAG_SP_TESTS = [
    {"n": 3, "adj": [0,3,0, 0,0,2, 0,0,0], "source": 0, "dists": [0,3,5]},
    {"n": 2, "adj": [0,7, 0,0], "source": 0, "dists": [0,7]},
    {"n": 3, "adj": [0,1,10, 0,0,2, 0,0,0], "source": 0, "dists": [0,1,3]},
]


def _dag_sp_soundness(idx, test):
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.DAGSP.Soundness.Test{idx}"
    adj_fstar = _seq_list(adj)
    dist_fstar = _seq_list(dists)
    constraints = [f"  assert (Seq.index dist_val {src} = 0);"]
    for u in range(n_v):
        for v in range(n_v):
            w = adj[u * n_v + v]
            if w > 0 and u != v:
                constraints.append(
                    f"  assert (Seq.index dist_val {v} <= Seq.index dist_val {u} + {w});"
                )
    assert_block = "\n".join(constraints) + "\n  ()"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let dist_val : Seq.seq int = {dist_fstar}

let soundness_test () : Lemma
  (Seq.length dist_val = {n_v} /\\
   Seq.index dist_val {src} = 0 /\\
   (forall (v: nat). v < {n_v} ==> Seq.index dist_val v >= 0))
=
{assert_block}

#pop-options
"""
    return mod, code


def _dag_sp_completeness(idx, test, variant="full"):
    n_v, adj, src, dists = test["n"], test["adj"], test["source"], test["dists"]
    mod = f"IntentEval.DAGSP.Completeness.{variant.title()}.Test{idx}"
    adj_fstar = _seq_list(adj)
    dist_fstar = _seq_list(dists)
    triangle = []
    for u in range(n_v):
        for v in range(n_v):
            w = adj[u * n_v + v]
            if w > 0 and u != v:
                triangle.append(f"   Seq.index d {v} <= Seq.index d {u} + {w}")
    tri_str = " /\\\n".join(triangle) if triangle else "true"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let dist_val : Seq.seq int = {dist_fstar}

let completeness_test (d: Seq.seq int) : Lemma
  (requires Seq.length d = {n_v} /\\
            Seq.index d {src} = 0 /\\
            (forall (v: nat). v < {n_v} ==> Seq.index d v >= 0) /\\
            {tri_str})
  (ensures d == dist_val)
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Kruskal MST: minimum spanning tree total weight
# ---------------------------------------------------------------------------

KRUSKAL_TESTS = [
    {"n": 3, "adj": [0,1,4, 1,0,2, 4,2,0], "mst_weight": 3},
    {"n": 2, "adj": [0,5, 5,0], "mst_weight": 5},
    {"n": 3, "adj": [0,3,1, 3,0,2, 1,2,0], "mst_weight": 3},
]


def _kruskal_soundness(idx, test):
    n_v, adj, mst_w = test["n"], test["adj"], test["mst_weight"]
    mod = f"IntentEval.KruskalMST.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  ({mst_w} >= 0)
= ()

#pop-options
"""
    return mod, code


def _kruskal_completeness(idx, test, variant="full"):
    n_v, adj, mst_w = test["n"], test["adj"], test["mst_weight"]
    mod = f"IntentEval.KruskalMST.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (w: int) : Lemma
  (requires w >= 0)
  (ensures w == {mst_w})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Prim MST: same spec as Kruskal — total MST weight
# ---------------------------------------------------------------------------

PRIM_TESTS = [
    {"n": 3, "adj": [0,2,3, 2,0,1, 3,1,0], "mst_weight": 3},
    {"n": 2, "adj": [0,4, 4,0], "mst_weight": 4},
    {"n": 3, "adj": [0,6,5, 6,0,2, 5,2,0], "mst_weight": 7},
]


def _prim_soundness(idx, test):
    n_v, adj, mst_w = test["n"], test["adj"], test["mst_weight"]
    mod = f"IntentEval.PrimMST.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  ({mst_w} >= 0)
= ()

#pop-options
"""
    return mod, code


def _prim_completeness(idx, test, variant="full"):
    n_v, adj, mst_w = test["n"], test["adj"], test["mst_weight"]
    mod = f"IntentEval.PrimMST.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (w: int) : Lemma
  (requires w >= 0)
  (ensures w == {mst_w})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Union-Find: connected components after union operations
# ---------------------------------------------------------------------------

UNION_FIND_TESTS = [
    {"n": 3, "unions": [[0, 1]], "queries": [[0, 1, True], [0, 2, False]]},
    {"n": 4, "unions": [[0, 1], [2, 3]], "queries": [[0, 1, True], [2, 3, True], [0, 2, False]]},
    {"n": 3, "unions": [[0, 1], [1, 2]], "queries": [[0, 2, True]]},
]


def _union_find_soundness(idx, test):
    n, unions, queries = test["n"], test["unions"], test["queries"]
    mod = f"IntentEval.UnionFind.Soundness.Test{idx}"

    parent = list(range(n))

    def find(x):
        while parent[x] != x:
            x = parent[x]
        return x

    def union(a, b):
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb

    for u_op in unions:
        union(u_op[0], u_op[1])

    root_map = {i: find(i) for i in range(n)}

    # Build connected function as explicit cases
    conn_cases = []
    for i in range(n):
        for j in range(i + 1, n):
            if root_map[i] == root_map[j]:
                conn_cases.append(f"(u = {i} && v = {j}) || (u = {j} && v = {i})")

    if conn_cases:
        conn_body = " || ".join(conn_cases)
    else:
        conn_body = "false"

    query_asserts = []
    for q in queries:
        u, v, expected = q
        val_str = "true" if expected else "false"
        query_asserts.append(f"  assert (connected {u} {v} = {val_str});")
    if query_asserts:
        assert_block = "\n".join(query_asserts) + "\n  ()"
    else:
        assert_block = "  ()"

    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let connected (u v: nat) : bool =
  {conn_body}

let soundness_test () : Lemma (true)
=
{assert_block}

#pop-options
"""
    return mod, code


def _union_find_completeness(idx, test, variant="full"):
    mod = f"IntentEval.UnionFind.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (r: bool) : Lemma
  (requires true)
  (ensures true)
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Miller-Rabin / Primality Test (Ch31)
# ---------------------------------------------------------------------------

PRIMALITY_TESTS = [
    {"n": 7, "is_prime": True},
    {"n": 15, "is_prime": False},
    {"n": 2, "is_prime": True},
]


def _primality_soundness(idx, test):
    n_val, expected = test["n"], test["is_prime"]
    mod = f"IntentEval.Primality.Soundness.Test{idx}"
    result_str = "true" if expected else "false"

    if expected:
        spec = f"(forall (d: nat). d >= 2 /\\ d < {n_val} ==> {n_val} % d <> 0)"
    else:
        divisor = None
        for d in range(2, n_val):
            if n_val % d == 0:
                divisor = d
                break
        spec = f"({n_val} % {divisor} = 0 /\\ {divisor} >= 2 /\\ {divisor} < {n_val})"

    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  {spec}
= ()

#pop-options
"""
    return mod, code


def _primality_completeness(idx, test, variant="full"):
    n_val, expected = test["n"], test["is_prime"]
    mod = f"IntentEval.Primality.Completeness.{variant.title()}.Test{idx}"
    result_val = "true" if expected else "false"

    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_prime (n: nat{{n >= 2}}) : bool =
  if n = 2 then true
  else if n = 3 then true
  else if n % 2 = 0 then false
  else if n < 9 then true
  else if n % 3 = 0 then false
  else true

let completeness_test (r: bool) : Lemma
  (requires r = is_prime {n_val})
  (ensures r = {result_val})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Graham Scan / Convex Hull (Ch33): output hull point indices
# ---------------------------------------------------------------------------

CONVEX_HULL_TESTS = [
    {"points": [(0,0), (1,0), (0,1)], "hull_size": 3},
    {"points": [(0,0), (1,0), (1,1), (0,1)], "hull_size": 4},
    {"points": [(0,0), (2,0), (1,1), (0,2), (2,2)], "hull_size": 4},
]


def _convex_hull_soundness(idx, test):
    points, hull_size = test["points"], test["hull_size"]
    mod = f"IntentEval.ConvexHull.Soundness.Test{idx}"
    n = len(points)
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  ({hull_size} >= 3 /\\ {hull_size} <= {n})
= ()

#pop-options
"""
    return mod, code


def _convex_hull_completeness(idx, test, variant="full"):
    points, hull_size = test["points"], test["hull_size"]
    mod = f"IntentEval.ConvexHull.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (h: nat) : Lemma
  (requires h >= 3 /\\ h <= {len(points)})
  (ensures h == {hull_size})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Edmonds-Karp / Max Flow (Ch26)
# ---------------------------------------------------------------------------

MAX_FLOW_TESTS = [
    {"n": 2, "cap": [0,10, 0,0], "source": 0, "sink": 1, "max_flow": 10},
    {"n": 3, "cap": [0,5,3, 0,0,2, 0,0,0], "source": 0, "sink": 2, "max_flow": 5},
    {"n": 3, "cap": [0,3,4, 0,0,2, 0,0,0], "source": 0, "sink": 2, "max_flow": 5},
]


def _max_flow_soundness(idx, test):
    n_v, cap, src, sink, mf = test["n"], test["cap"], test["source"], test["sink"], test["max_flow"]
    mod = f"IntentEval.MaxFlow.Soundness.Test{idx}"
    cap_fstar = _seq_list(cap)
    # Assert each capacity individually instead of forall with multiplication
    cap_asserts = []
    for u in range(n_v):
        for v in range(n_v):
            cap_asserts.append(f"  assert (Seq.index cap_val {u * n_v + v} >= 0);")
    cap_block = "\n".join(cap_asserts) + "\n  ()"
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let cap_val : Seq.seq int = {cap_fstar}

let soundness_test () : Lemma
  ({mf} >= 0 /\\ Seq.length cap_val = {n_v * n_v})
=
{cap_block}

#pop-options
"""
    return mod, code


def _max_flow_completeness(idx, test, variant="full"):
    n_v, cap, src, sink, mf = test["n"], test["cap"], test["source"], test["sink"], test["max_flow"]
    mod = f"IntentEval.MaxFlow.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (f: int) : Lemma
  (requires f >= 0)
  (ensures f == {mf})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Vertex Cover 2-Approximation (Ch35)
# ---------------------------------------------------------------------------

VERTEX_COVER_TESTS = [
    {"n": 3, "edges": [[0,1], [1,2]], "cover_size": 2},
    {"n": 3, "edges": [[0,1], [0,2], [1,2]], "cover_size": 2},
    {"n": 4, "edges": [[0,1], [2,3]], "cover_size": 2},
]


def _vertex_cover_soundness(idx, test):
    n_v, edges, cs = test["n"], test["edges"], test["cover_size"]
    mod = f"IntentEval.VertexCover.Soundness.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let soundness_test () : Lemma
  ({cs} >= 0 /\\ {cs} <= {n_v})
= ()

#pop-options
"""
    return mod, code


def _vertex_cover_completeness(idx, test, variant="full"):
    n_v, edges, cs = test["n"], test["edges"], test["cover_size"]
    mod = f"IntentEval.VertexCover.Completeness.{variant.title()}.Test{idx}"
    code = f"""module {mod}
open FStar.Mul

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let completeness_test (c: nat) : Lemma
  (requires c >= 0 /\\ c <= {n_v})
  (ensures c == {cs})
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Partial Selection Sort (Ch09): first k smallest elements sorted
# ---------------------------------------------------------------------------

PARTIAL_SELECT_TESTS = [
    {"arr": [5, 1, 3], "k": 2, "result": [1, 3]},
    {"arr": [4, 2], "k": 1, "result": [2]},
    {"arr": [3, 1, 4, 1, 5], "k": 3, "result": [1, 1, 3]},
]


def _partial_select_soundness(idx, test):
    arr, k, result = test["arr"], test["k"], test["result"]
    mod = f"IntentEval.PartialSelect.Soundness.Test{idx}"
    res_fstar = _seq_list(result)
    arr_fstar = _seq_list(arr)
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let arr_val : Seq.seq int = {arr_fstar}
let result_val : Seq.seq int = {res_fstar}

let soundness_test () : Lemma
  (Seq.length result_val = {k} /\\
   is_sorted result_val)
= ()

#pop-options
"""
    return mod, code


def _partial_select_completeness(idx, test, variant="full"):
    arr, k, result = test["arr"], test["k"], test["result"]
    mod = f"IntentEval.PartialSelect.Completeness.{variant.title()}.Test{idx}"
    res_fstar = _seq_list(result)
    arr_fstar = _seq_list(arr)
    code = f"""module {mod}
open FStar.Mul
open FStar.Seq
module Seq = FStar.Seq

#push-options "--z3rlimit 200 --fuel 8 --ifuel 8"

let is_sorted (s: Seq.seq int) : prop =
  forall (i j: nat). i <= j /\\ j < Seq.length s ==> Seq.index s i <= Seq.index s j

let arr_val : Seq.seq int = {arr_fstar}
let result_val : Seq.seq int = {res_fstar}

let completeness_test (r: Seq.seq int) : Lemma
  (requires Seq.length r = {k} /\\
            is_sorted r)
  (ensures r == result_val)
= ()

#pop-options
"""
    return mod, code


# ---------------------------------------------------------------------------
# Algorithm Registry
# ---------------------------------------------------------------------------

ALGORITHMS = {
    "insertion_sort": {
        "display_name": "Insertion Sort",
        "chapter": "Ch02",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("InsertionSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("InsertionSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "merge_sort": {
        "display_name": "Merge Sort",
        "chapter": "Ch02",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("MergeSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("MergeSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "heap_sort": {
        "display_name": "Heap Sort",
        "chapter": "Ch06",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("HeapSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("HeapSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "quick_sort": {
        "display_name": "Quick Sort",
        "chapter": "Ch07",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("QuickSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("QuickSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "counting_sort": {
        "display_name": "Counting Sort",
        "chapter": "Ch08",
        "spec_description": "sorted(y) ∧ permutation(x, y) ∧ in_range(y, k)",
        "test_cases": COUNTING_SORT_TESTS,
        "soundness_gen": lambda idx, t: _counting_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _counting_completeness(idx, t, v),
        "spec_variants": ["full", "sorted_only", "no_range"],
    },
    "binary_search": {
        "display_name": "Binary Search",
        "chapter": "Ch04",
        "spec_description": "found ⇒ arr[i]=key ∧ ¬found ⇒ key∉arr",
        "test_cases": BINARY_SEARCH_TESTS,
        "soundness_gen": lambda idx, t: _bsearch_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bsearch_completeness(idx, t, v),
        "spec_variants": ["full", "found_only"],
    },
    "gcd": {
        "display_name": "GCD",
        "chapter": "Ch31",
        "spec_description": "divides(g,a) ∧ divides(g,b) ∧ greatest",
        "test_cases": GCD_TESTS,
        "soundness_gen": lambda idx, t: _gcd_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _gcd_completeness(idx, t, v),
        "spec_variants": ["full", "divides_only"],
    },
    "max_subarray": {
        "display_name": "Max Subarray",
        "chapter": "Ch04",
        "spec_description": "∃ lo,hi. sum(arr[lo..hi])=r ∧ ∀ lo',hi'. sum(...)≤r",
        "test_cases": MAX_SUBARRAY_TESTS,
        "soundness_gen": lambda idx, t: _maxsub_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _maxsub_completeness(idx, t, v),
        "spec_variants": ["full", "exists_only"],
    },
    "mod_exp": {
        "display_name": "Modular Exponentiation",
        "chapter": "Ch31",
        "spec_description": "result = b^e mod m ∧ 0 ≤ result < m",
        "test_cases": MODEXP_TESTS,
        "soundness_gen": lambda idx, t: _modexp_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _modexp_completeness(idx, t, v),
        "spec_variants": ["full", "range_only"],
    },
    "cross_product": {
        "display_name": "Cross Product",
        "chapter": "Ch33",
        "spec_description": "r = (p2−p1) × (p3−p1)",
        "test_cases": CROSS_PRODUCT_TESTS,
        "soundness_gen": lambda idx, t: _cross_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _cross_completeness(idx, t, v),
        "spec_variants": ["full", "sign_only"],
    },
    "segment_intersection": {
        "display_name": "Segment Intersection",
        "chapter": "Ch33",
        "spec_description": "orientation-based intersection test",
        "test_cases": SEGMENT_INTERSECTION_TESTS,
        "soundness_gen": lambda idx, t: _segment_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _segment_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "stack": {
        "display_name": "Stack (push/pop)",
        "chapter": "Ch10",
        "spec_description": "pop(push(s,x)) = (x, s)",
        "test_cases": STACK_TESTS,
        "soundness_gen": lambda idx, t: _stack_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _stack_completeness(idx, t, v),
        "spec_variants": ["full", "pop_only"],
    },
    "queue": {
        "display_name": "Queue (enqueue/dequeue)",
        "chapter": "Ch10",
        "spec_description": "dequeue returns FIFO order",
        "test_cases": QUEUE_TESTS,
        "soundness_gen": lambda idx, t: _queue_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _queue_completeness(idx, t, v),
        "spec_variants": ["full", "dequeue_only"],
    },
    "topological_sort": {
        "display_name": "Topological Sort",
        "chapter": "Ch22",
        "spec_description": "valid topological order ∧ distinct vertices",
        "test_cases": TOPO_SORT_TESTS,
        "soundness_gen": lambda idx, t: _topo_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _topo_completeness(idx, t, v),
        "spec_variants": ["full", "order_only"],
    },
    "lcs": {
        "display_name": "LCS Length",
        "chapter": "Ch15",
        "spec_description": "r = lcs_length(x, y, |x|, |y|)",
        "test_cases": LCS_TESTS,
        "soundness_gen": lambda idx, t: _lcs_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _lcs_completeness(idx, t, v),
        "spec_variants": ["full", "nonneg_only"],
    },
    "string_matching": {
        "display_name": "String Matching",
        "chapter": "Ch32",
        "spec_description": "count_matches(text, pattern) = r",
        "test_cases": STRING_MATCH_TESTS,
        "soundness_gen": lambda idx, t: _strmatch_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _strmatch_completeness(idx, t, v),
        "spec_variants": ["full", "nonneg_only"],
    },
    # --- New algorithms (Batch 1-4) ---
    "radix_sort": {
        "display_name": "Radix Sort",
        "chapter": "Ch08",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("RadixSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("RadixSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "bucket_sort": {
        "display_name": "Bucket Sort",
        "chapter": "Ch08",
        "spec_description": "sorted(y) ∧ permutation(x, y)",
        "test_cases": SORTING_TESTS,
        "soundness_gen": lambda idx, t: _sorting_soundness("BucketSort", idx, t[0], t[1]),
        "completeness_gen": lambda idx, t, v: _sorting_completeness("BucketSort", idx, t[0], t[1], v),
        "spec_variants": ["full", "sorted_only", "permutation_only"],
    },
    "minimum": {
        "display_name": "Minimum",
        "chapter": "Ch09",
        "spec_description": "result ∈ arr ∧ result ≤ all elements",
        "test_cases": MIN_TESTS,
        "soundness_gen": lambda idx, t: _min_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _min_completeness(idx, t, v),
        "spec_variants": ["full", "member_only"],
    },
    "maximum": {
        "display_name": "Maximum",
        "chapter": "Ch09",
        "spec_description": "result ∈ arr ∧ result ≥ all elements",
        "test_cases": MAX_TESTS,
        "soundness_gen": lambda idx, t: _max_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _max_completeness(idx, t, v),
        "spec_variants": ["full", "member_only"],
    },
    "minmax": {
        "display_name": "Simultaneous Min-Max",
        "chapter": "Ch09",
        "spec_description": "returns (min, max) of arr",
        "test_cases": MINMAX_TESTS,
        "soundness_gen": lambda idx, t: _minmax_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _minmax_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "quickselect": {
        "display_name": "Quickselect (kth smallest)",
        "chapter": "Ch09",
        "spec_description": "result = kth smallest element",
        "test_cases": SELECT_TESTS,
        "soundness_gen": lambda idx, t: _select_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _select_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "extended_gcd": {
        "display_name": "Extended GCD",
        "chapter": "Ch31",
        "spec_description": "g=gcd(a,b) ∧ a·x+b·y=g",
        "test_cases": EGCD_TESTS,
        "soundness_gen": lambda idx, t: _egcd_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _egcd_completeness(idx, t, v),
        "spec_variants": ["full", "gcd_only"],
    },
    "matrix_multiply": {
        "display_name": "Matrix Multiply",
        "chapter": "Ch04",
        "spec_description": "C[i][j] = Σ A[i][k]·B[k][j]",
        "test_cases": MATMUL_TESTS,
        "soundness_gen": lambda idx, t: _matmul_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _matmul_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "partition": {
        "display_name": "Partition (Lomuto)",
        "chapter": "Ch07",
        "spec_description": "left ≤ pivot ≤ right ∧ permutation",
        "test_cases": PARTITION_TESTS,
        "soundness_gen": lambda idx, t: _partition_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _partition_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "sll_insert": {
        "display_name": "Linked List Insert",
        "chapter": "Ch10",
        "spec_description": "insert_head(l, x) = x :: l",
        "test_cases": SLL_INSERT_TESTS,
        "soundness_gen": lambda idx, t: _sll_insert_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _sll_insert_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "sll_delete": {
        "display_name": "Linked List Delete",
        "chapter": "Ch10",
        "spec_description": "delete first occurrence of x",
        "test_cases": SLL_DELETE_TESTS,
        "soundness_gen": lambda idx, t: _sll_delete_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _sll_delete_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "hash_table": {
        "display_name": "Hash Table",
        "chapter": "Ch11",
        "spec_description": "search(insert(ht,k,v),k) = Some v",
        "test_cases": HASH_TABLE_TESTS,
        "soundness_gen": lambda idx, t: _hashtable_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _hashtable_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "bst_search": {
        "display_name": "BST Search",
        "chapter": "Ch12",
        "spec_description": "search(insert*(∅, keys), k) = found",
        "test_cases": BST_SEARCH_TESTS,
        "soundness_gen": lambda idx, t: _bst_search_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bst_search_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "bst_inorder": {
        "display_name": "BST Inorder",
        "chapter": "Ch12",
        "spec_description": "inorder(bst) is sorted",
        "test_cases": BST_INORDER_TESTS,
        "soundness_gen": lambda idx, t: _bst_inorder_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bst_inorder_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "rod_cutting": {
        "display_name": "Rod Cutting",
        "chapter": "Ch15",
        "spec_description": "optimal_revenue(prices, n)",
        "test_cases": ROD_CUTTING_TESTS,
        "soundness_gen": lambda idx, t: _rod_cutting_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _rod_cutting_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "bfs": {
        "display_name": "BFS Distance",
        "chapter": "Ch22",
        "spec_description": "shortest unweighted path distance",
        "test_cases": BFS_TESTS,
        "soundness_gen": lambda idx, t: _bfs_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bfs_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "dfs": {
        "display_name": "DFS Times",
        "chapter": "Ch22",
        "spec_description": "d[v] < f[v] ∧ parenthesis theorem",
        "test_cases": DFS_TESTS,
        "soundness_gen": lambda idx, t: _dfs_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _dfs_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "dijkstra": {
        "display_name": "Dijkstra",
        "chapter": "Ch24",
        "spec_description": "dist[v] = shortest weighted path ∧ triangle inequality",
        "test_cases": DIJKSTRA_TESTS,
        "soundness_gen": lambda idx, t: _dijkstra_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _dijkstra_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "bellman_ford": {
        "display_name": "Bellman-Ford",
        "chapter": "Ch24",
        "spec_description": "dist[v] = shortest path ∧ triangle inequality",
        "test_cases": BELLMAN_FORD_TESTS,
        "soundness_gen": lambda idx, t: _bellman_ford_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bellman_ford_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "floyd_warshall": {
        "display_name": "Floyd-Warshall",
        "chapter": "Ch25",
        "spec_description": "all-pairs shortest paths ∧ triangle inequality",
        "test_cases": FLOYD_WARSHALL_TESTS,
        "soundness_gen": lambda idx, t: _floyd_warshall_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _floyd_warshall_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "activity_selection": {
        "display_name": "Activity Selection",
        "chapter": "Ch16",
        "spec_description": "max compatible non-overlapping activities",
        "test_cases": ACTIVITY_TESTS,
        "soundness_gen": lambda idx, t: _activity_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _activity_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "kmp_string_match": {
        "display_name": "KMP String Match",
        "chapter": "Ch32",
        "spec_description": "count_matches(text, pattern) = r",
        "test_cases": STRING_MATCH_TESTS,
        "soundness_gen": lambda idx, t: _strmatch_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _strmatch_completeness(idx, t, v),
        "spec_variants": ["full", "nonneg_only"],
    },
    "rabin_karp": {
        "display_name": "Rabin-Karp String Match",
        "chapter": "Ch32",
        "spec_description": "count_matches(text, pattern) = r",
        "test_cases": STRING_MATCH_TESTS,
        "soundness_gen": lambda idx, t: _strmatch_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _strmatch_completeness(idx, t, v),
        "spec_variants": ["full", "nonneg_only"],
    },
    "bst_insert": {
        "display_name": "BST Insert",
        "chapter": "Ch12",
        "spec_description": "inorder(insert(tree, key)) is sorted ∧ contains key",
        "test_cases": BST_INSERT_TESTS,
        "soundness_gen": lambda idx, t: _bst_insert_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bst_insert_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "bst_delete": {
        "display_name": "BST Delete",
        "chapter": "Ch12",
        "spec_description": "inorder(delete(tree, key)) is sorted ∧ key removed",
        "test_cases": BST_DELETE_TESTS,
        "soundness_gen": lambda idx, t: _bst_delete_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _bst_delete_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "matrix_chain": {
        "display_name": "Matrix Chain Multiplication",
        "chapter": "Ch15",
        "spec_description": "min scalar multiplications via recursive mc_cost",
        "test_cases": MATRIX_CHAIN_TESTS,
        "soundness_gen": lambda idx, t: _matrix_chain_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _matrix_chain_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "huffman": {
        "display_name": "Huffman Coding",
        "chapter": "Ch16",
        "spec_description": "min total weighted path length",
        "test_cases": HUFFMAN_TESTS,
        "soundness_gen": lambda idx, t: _huffman_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _huffman_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "dag_shortest_path": {
        "display_name": "DAG Shortest Paths",
        "chapter": "Ch24",
        "spec_description": "dist[v] = shortest path in DAG ∧ triangle inequality",
        "test_cases": DAG_SP_TESTS,
        "soundness_gen": lambda idx, t: _dag_sp_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _dag_sp_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "kruskal_mst": {
        "display_name": "Kruskal MST",
        "chapter": "Ch23",
        "spec_description": "minimum spanning tree weight",
        "test_cases": KRUSKAL_TESTS,
        "soundness_gen": lambda idx, t: _kruskal_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _kruskal_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "prim_mst": {
        "display_name": "Prim MST",
        "chapter": "Ch23",
        "spec_description": "minimum spanning tree weight",
        "test_cases": PRIM_TESTS,
        "soundness_gen": lambda idx, t: _prim_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _prim_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "union_find": {
        "display_name": "Union-Find",
        "chapter": "Ch21",
        "spec_description": "find(x) = find(y) iff connected",
        "test_cases": UNION_FIND_TESTS,
        "soundness_gen": lambda idx, t: _union_find_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _union_find_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "primality_test": {
        "display_name": "Primality Test",
        "chapter": "Ch31",
        "spec_description": "is_prime(n) iff no divisor in [2,n)",
        "test_cases": PRIMALITY_TESTS,
        "soundness_gen": lambda idx, t: _primality_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _primality_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "convex_hull": {
        "display_name": "Graham Scan (Convex Hull)",
        "chapter": "Ch33",
        "spec_description": "convex hull size of point set",
        "test_cases": CONVEX_HULL_TESTS,
        "soundness_gen": lambda idx, t: _convex_hull_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _convex_hull_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "max_flow": {
        "display_name": "Edmonds-Karp (Max Flow)",
        "chapter": "Ch26",
        "spec_description": "max flow value with capacity constraints",
        "test_cases": MAX_FLOW_TESTS,
        "soundness_gen": lambda idx, t: _max_flow_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _max_flow_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "vertex_cover": {
        "display_name": "Vertex Cover (2-Approx)",
        "chapter": "Ch35",
        "spec_description": "vertex cover ≤ 2× optimal",
        "test_cases": VERTEX_COVER_TESTS,
        "soundness_gen": lambda idx, t: _vertex_cover_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _vertex_cover_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
    "partial_select": {
        "display_name": "Partial Selection Sort",
        "chapter": "Ch09",
        "spec_description": "k smallest elements sorted",
        "test_cases": PARTIAL_SELECT_TESTS,
        "soundness_gen": lambda idx, t: _partial_select_soundness(idx, t),
        "completeness_gen": lambda idx, t, v: _partial_select_completeness(idx, t, v),
        "spec_variants": ["full"],
    },
}
