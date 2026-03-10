"""
Intent Formalization Agent — Specification Evaluator

Evaluates F* specifications using symbolic testing (FMCAD 2024 paper).

Soundness: Does the spec hold on known-good test inputs/outputs?
Completeness (Appendix B): Does the spec uniquely determine the output?

Usage:
  python agent/run_eval.py --algorithm insertion_sort
  python agent/run_eval.py --all-algorithms --per-test-timeout 30
  python agent/run_eval.py --algorithm gcd --all-variants
"""

import sys, io
sys.stdout = io.TextIOWrapper(sys.stdout.buffer, encoding='utf-8', errors='replace')

import argparse
import os
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import List, Tuple

from algorithms import ALGORITHMS

# Paths — adjust WSL_AUTOCLRS if your build is elsewhere
WSL_AUTOCLRS = os.environ.get("WSL_AUTOCLRS", "~/AutoCLRS")
WSL_FSTAR_EXE = f"{WSL_AUTOCLRS}/FStar/bin/fstar.exe"
WSL_PULSE_LIB = f"{WSL_AUTOCLRS}/pulse/out/lib/pulse"

TIMEOUT_SECONDS = 600


def win_to_wsl_path(win_path: str) -> str:
    """Convert a Windows path to WSL path."""
    drive = win_path[0].lower()
    rest = win_path[2:].replace("\\", "/")
    return f"/mnt/{drive}{rest}"


def run_fstar_via_script(fstar_code: str, module_name: str,
                         timeout: int = TIMEOUT_SECONDS) -> Tuple[bool, str]:
    """Run F* via a helper bash script in WSL."""
    temp_dir = Path(tempfile.gettempdir()) / "intent_eval"
    temp_dir.mkdir(exist_ok=True)

    fstar_filename = module_name + ".fst"
    fstar_path = temp_dir / fstar_filename
    fstar_path.write_bytes(fstar_code.encode("utf-8").replace(b"\r\n", b"\n"))

    wsl_temp = win_to_wsl_path(str(temp_dir))
    wsl_file = f"{wsl_temp}/{fstar_filename}"

    script_content = (
        f"#!/bin/bash\n"
        f"set -euo pipefail\n"
        f"eval $(opam env)\n"
        f"{WSL_FSTAR_EXE} --include {WSL_PULSE_LIB} {wsl_file} 2>&1\n"
    )
    script_path = temp_dir / f"run_{module_name}.sh"
    script_path.write_bytes(script_content.encode("utf-8"))
    wsl_script = f"{wsl_temp}/run_{module_name}.sh"

    try:
        result = subprocess.run(
            ["wsl", "-d", "Ubuntu", "--", "bash", wsl_script],
            capture_output=True, text=True,
            timeout=timeout
        )
        output = result.stdout + result.stderr
        success = "All verification conditions discharged successfully" in output
        return success, output.strip()
    except subprocess.TimeoutExpired:
        return False, f"TIMEOUT after {timeout}s"
    except Exception as e:
        return False, f"ERROR: {e}"


def _run_check(label, module_name, code, timeout):
    """Run a single F* check. Returns (passed, skipped, elapsed, output)."""
    print(f"  {label} ... ", end="", flush=True)
    t0 = time.time()
    success, output = run_fstar_via_script(code, module_name, timeout=timeout)
    elapsed = time.time() - t0
    is_timeout = "TIMEOUT" in output

    if is_timeout:
        print(f"⏭ SKIP ({elapsed:.1f}s)")
    elif success:
        print(f"✓ PASS ({elapsed:.1f}s)")
    else:
        print(f"✗ FAIL ({elapsed:.1f}s)")
        for line in output.split("\n"):
            if "Error" in line or "error" in line:
                print(f"    {line.strip()}")
                break
    return success, is_timeout, elapsed


def evaluate_algorithm(algo_key: str, variant: str = "full",
                       per_test_timeout: int = 60,
                       max_tests: int = None) -> dict:
    """Evaluate one algorithm for one spec variant."""
    algo = ALGORITHMS[algo_key]
    tests = algo["test_cases"]
    if max_tests:
        tests = tests[:max_tests]

    print(f"\n{'=' * 70}")
    print(f"  {algo['display_name']} ({algo['chapter']})")
    print(f"  Spec: {algo['spec_description']}")
    print(f"  Variant: {variant}  |  Tests: {len(tests)}  |  Timeout: {per_test_timeout}s")
    print(f"{'=' * 70}")

    results = {"algorithm": algo_key, "variant": variant,
               "soundness": [], "completeness": []}

    # --- Soundness ---
    print("\n  Soundness:")
    s_pass = s_skip = 0
    for idx, test in enumerate(tests):
        mod_name, code = algo["soundness_gen"](idx, test)
        passed, skipped, elapsed = _run_check(
            f"Test {idx}", mod_name, code, per_test_timeout)
        results["soundness"].append({"passed": passed, "skipped": skipped, "time": elapsed})
        if skipped:
            s_skip += 1
        elif passed:
            s_pass += 1

    s_ran = len(tests) - s_skip

    # --- Completeness ---
    print(f"\n  Completeness ({variant}):")
    c_pass = c_skip = 0
    for idx, test in enumerate(tests):
        mod_name, code = algo["completeness_gen"](idx, test, variant)
        passed, skipped, elapsed = _run_check(
            f"Test {idx}", mod_name, code, per_test_timeout)
        results["completeness"].append({"passed": passed, "skipped": skipped, "time": elapsed})
        if skipped:
            c_skip += 1
        elif passed:
            c_pass += 1

    c_ran = len(tests) - c_skip

    # --- Summary line ---
    s_label = "SOUND" if s_pass == s_ran else "NOT SOUND"
    c_label = "COMPLETE" if c_pass == c_ran else "INCOMPLETE"
    s_extra = f" ({s_skip} skipped)" if s_skip else ""
    c_extra = f" ({c_skip} skipped)" if c_skip else ""
    print(f"\n  Result: Soundness {s_pass}/{s_ran} {s_label}{s_extra}"
          f"  |  Completeness {c_pass}/{c_ran} {c_label}{c_extra}")

    results["sound"] = s_pass == s_ran
    results["complete"] = c_pass == c_ran
    results["s_pass"] = s_pass
    results["s_ran"] = s_ran
    results["c_pass"] = c_pass
    results["c_ran"] = c_ran
    return results


def main():
    parser = argparse.ArgumentParser(
        description="Evaluate specification quality via symbolic testing"
    )
    parser.add_argument(
        "--algorithm",
        choices=list(ALGORITHMS.keys()),
        default=None,
        help="Run a single algorithm"
    )
    parser.add_argument(
        "--all-algorithms",
        action="store_true",
        help="Run all registered algorithms"
    )
    parser.add_argument(
        "--spec-variant",
        default="full",
        help="Spec variant to evaluate (default: full)"
    )
    parser.add_argument(
        "--all-variants",
        action="store_true",
        help="Evaluate all spec variants for each algorithm"
    )
    parser.add_argument(
        "--max-tests",
        type=int,
        default=None,
        help="Limit number of tests per algorithm"
    )
    parser.add_argument(
        "--per-test-timeout",
        type=int,
        default=30,
        help="Seconds before skipping a slow test (default: 30)"
    )
    args = parser.parse_args()

    # Determine which algorithms to run
    if args.all_algorithms:
        algo_keys = list(ALGORITHMS.keys())
    elif args.algorithm:
        algo_keys = [args.algorithm]
    else:
        algo_keys = ["insertion_sort"]

    all_results = []
    for key in algo_keys:
        algo = ALGORITHMS[key]
        if args.all_variants:
            variants = algo["spec_variants"]
        else:
            variants = [args.spec_variant if args.spec_variant in algo["spec_variants"]
                        else algo["spec_variants"][0]]
        for variant in variants:
            result = evaluate_algorithm(
                key, variant=variant,
                per_test_timeout=args.per_test_timeout,
                max_tests=args.max_tests
            )
            all_results.append(result)

    # Final summary table
    print(f"\n\n{'#' * 70}")
    print("FINAL REPORT")
    print(f"{'#' * 70}")
    print(f"{'Algorithm':<25} {'Variant':<20} {'Soundness':<15} {'Completeness':<15}")
    print("-" * 75)
    for r in all_results:
        algo = ALGORITHMS[r["algorithm"]]
        s_str = f"{r['s_pass']}/{r['s_ran']}"
        c_str = f"{r['c_pass']}/{r['c_ran']}"
        s_ok = "✓" if r["sound"] else "✗"
        c_ok = "✓" if r["complete"] else "✗"
        print(f"{algo['display_name']:<25} {r['variant']:<20} {s_ok} {s_str:<12} {c_ok} {c_str:<12}")


if __name__ == "__main__":
    main()
