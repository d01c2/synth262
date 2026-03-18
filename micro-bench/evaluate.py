#!/usr/bin/env python3
"""
micro-bench evaluation: baseline -> comparison -> compare.

Usage: python3 evaluate.py [--trials N] [--duration D]
"""

import json
import re
import subprocess
import sys
import argparse
from pathlib import Path
from datetime import datetime

BENCH_DIR = Path(__file__).parent
PROJECT_DIR = BENCH_DIR.parent
RESULTS_DIR = BENCH_DIR / "results"
BENCHMARKS_FILE = BENCH_DIR / "benchmarks.jsonl"


def load_benchmarks():
    with open(BENCHMARKS_FILE) as f:
        return [json.loads(line) for line in f if line.strip()]


def run_single(branch, seed, duration, ablation=False):
    """Run a single mutation trial, return iteration count or None for timeout."""
    ablation_flag = " -mutate:ablation" if ablation else ""
    cmd = f'sbt -error "run mutate {seed} -mutate:branch={branch} -mutate:duration={duration}{ablation_flag}"'
    try:
        result = subprocess.run(
            cmd,
            shell=True,
            capture_output=True,
            text=True,
            cwd=str(PROJECT_DIR),
            timeout=duration + 60,
        )
        m = re.search(r"Covered in (\d+)", result.stdout + result.stderr)
        return int(m.group(1)) if m else None
    except subprocess.TimeoutExpired:
        return None


def run_benchmarks(label, trials, duration):
    """Run all benchmarks and save results."""
    RESULTS_DIR.mkdir(exist_ok=True)
    benchmarks = load_benchmarks()
    results = {}
    ablation = label == "baseline"

    for bench in benchmarks:
        bid = bench["id"]
        print(f"\n[{bid}]")
        iterations = []
        for t in range(1, trials + 1):
            it = run_single(bench["branch"], bench["seed"], duration, ablation)
            status = str(it) if it is not None else "TIMEOUT"
            print(f"  Trial {t}/{trials}: {status}")
            iterations.append(it)
            if it is None and t == 1:
                print(f"  Skipping remaining trials (first trial TIMEOUT)")
                break
        results[bid] = {
            "benchmark": bench,
            "iterations": iterations,
            "timestamp": datetime.now().isoformat(),
        }

    outfile = RESULTS_DIR / f"{label}.json"
    with open(outfile, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {outfile}")


def filter_iters(raw):
    """Split raw iterations into (successes, timeout_count)."""
    ok = [i for i in raw if i is not None]
    return ok, len(raw) - len(ok)


def compare():
    """Compare baseline vs comparison and generate box plot + summary."""
    try:
        import matplotlib

        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
        from matplotlib.patches import Patch
    except ImportError:
        print("matplotlib/numpy required: pip install matplotlib numpy")
        sys.exit(1)

    baseline_file = RESULTS_DIR / "baseline.json"
    comparison_file = RESULTS_DIR / "comparison.json"

    for f in [baseline_file, comparison_file]:
        if not f.exists():
            print(f"Missing {f}. Run evaluate.py first.")
            sys.exit(1)

    with open(baseline_file) as f:
        baseline = json.load(f)
    with open(comparison_file) as f:
        comparison = json.load(f)

    bench_ids = sorted(set(baseline.keys()) & set(comparison.keys()))
    colors = {"base": "#4C72B0", "comp": "#DD8452"}

    # --- Box plot ---
    fig, ax = plt.subplots(figsize=(12, 6))
    x = np.arange(len(bench_ids))
    labels = []
    for i, bid in enumerate(bench_ids):
        b_ok, _ = filter_iters(baseline[bid]["iterations"])
        c_ok, _ = filter_iters(comparison[bid]["iterations"])
        labels.append(bid)
        for data, pos, color in [
            (b_ok, i - 0.2, colors["base"]),
            (c_ok, i + 0.2, colors["comp"]),
        ]:
            if data:
                ax.boxplot(
                    [data],
                    positions=[pos],
                    widths=0.3,
                    patch_artist=True,
                    boxprops=dict(facecolor=color, alpha=0.7),
                )

    ax.set_xlabel("Benchmark")
    ax.set_ylabel("Iterations to Cover")
    ax.set_title("Distribution of Iterations (Baseline vs Comparison)")
    ax.set_xticks(x)
    ax.set_xticklabels(labels, rotation=45, ha="right")
    ax.legend(
        [Patch(facecolor=c, alpha=0.7) for c in colors.values()],
        ["Baseline", "Comparison"],
    )
    fig.tight_layout()
    fig.savefig(RESULTS_DIR / "box_plot.png", dpi=150)
    print(f"Box plot saved to {RESULTS_DIR / 'box_plot.png'}")

    # --- Summary table ---
    print("\n[Summary]")
    header = f"{'Benchmark':<20} {'Base Avg':>10} {'Comp Avg':>10} {'Speedup':>10} {'Base TO':>8} {'Comp TO':>8}"
    print(header)
    print("-" * len(header))
    for bid in bench_ids:
        b_ok, b_to = filter_iters(baseline[bid]["iterations"])
        c_ok, c_to = filter_iters(comparison[bid]["iterations"])
        b_avg = np.mean(b_ok) if b_ok else float("inf")
        c_avg = np.mean(c_ok) if c_ok else float("inf")
        speedup = b_avg / c_avg if c_avg > 0 else float("inf")
        print(
            f"{bid:<20} {b_avg:>10.1f} {c_avg:>10.1f} {speedup:>9.2f}x {b_to:>8} {c_to:>8}"
        )


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Micro-benchmark evaluation")
    parser.add_argument("--trials", type=int, default=10)
    parser.add_argument("--duration", type=int, default=60)
    args = parser.parse_args()

    run_benchmarks("baseline", args.trials, args.duration)
    run_benchmarks("comparison", args.trials, args.duration)
    compare()
