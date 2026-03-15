#!/usr/bin/env python3
"""Micro-benchmark runner and chart generator.

Usage:
  python3 run-benchmarks.py baseline [--trials N] [--duration D]
  python3 run-benchmarks.py improved [--trials N] [--duration D]
  python3 run-benchmarks.py compare
"""

import json
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
    benchmarks = []
    with open(BENCHMARKS_FILE) as f:
        for line in f:
            line = line.strip()
            if line:
                benchmarks.append(json.loads(line))
    return benchmarks


def run_single(branch, seed, duration):
    """Run a single mutation trial, return iteration count or None for timeout."""
    cmd = f'sbt -error "run mutate {seed} -mutate:branch={branch} -mutate:duration={duration}"'
    try:
        result = subprocess.run(
            cmd, shell=True, capture_output=True, text=True,
            cwd=str(PROJECT_DIR), timeout=duration + 60
        )
        output = result.stdout + result.stderr
        for line in output.split("\n"):
            if "Covered in" in line:
                # Extract the number after "Covered in"
                parts = line.split("Covered in")
                if len(parts) > 1:
                    num = "".join(c for c in parts[1].split()[0] if c.isdigit())
                    if num:
                        return int(num)
        return None  # timeout
    except subprocess.TimeoutExpired:
        return None


def run_benchmarks(label, trials, duration):
    """Run all benchmarks and save results."""
    RESULTS_DIR.mkdir(exist_ok=True)
    benchmarks = load_benchmarks()
    results = {}

    for bench in benchmarks:
        bid = bench["id"]
        print(f"\n=== {bid}: {bench['desc']} ===")
        iterations = []
        for t in range(1, trials + 1):
            it = run_single(bench["branch"], bench["seed"], duration)
            status = str(it) if it is not None else "TIMEOUT"
            print(f"  Trial {t}/{trials}: {status}")
            iterations.append(it)
        results[bid] = {
            "benchmark": bench,
            "iterations": iterations,
            "timestamp": datetime.now().isoformat(),
        }

    outfile = RESULTS_DIR / f"{label}.json"
    with open(outfile, "w") as f:
        json.dump(results, f, indent=2)
    print(f"\nResults saved to {outfile}")


def compare():
    """Compare baseline vs improved and generate charts."""
    try:
        import matplotlib
        matplotlib.use("Agg")
        import matplotlib.pyplot as plt
        import numpy as np
    except ImportError:
        print("matplotlib/numpy required: pip install matplotlib numpy")
        sys.exit(1)

    baseline_file = RESULTS_DIR / "baseline.json"
    improved_file = RESULTS_DIR / "improved.json"

    if not baseline_file.exists():
        print(f"Missing {baseline_file}. Run: python3 run-benchmarks.py baseline")
        sys.exit(1)
    if not improved_file.exists():
        print(f"Missing {improved_file}. Run: python3 run-benchmarks.py improved")
        sys.exit(1)

    with open(baseline_file) as f:
        baseline = json.load(f)
    with open(improved_file) as f:
        improved = json.load(f)

    bench_ids = sorted(set(baseline.keys()) & set(improved.keys()))

    # --- Bar chart: median iterations ---
    fig, ax = plt.subplots(figsize=(10, 6))
    x = np.arange(len(bench_ids))
    width = 0.35

    base_medians = []
    impr_medians = []
    for bid in bench_ids:
        b_iters = [i for i in baseline[bid]["iterations"] if i is not None]
        i_iters = [i for i in improved[bid]["iterations"] if i is not None]
        base_medians.append(np.median(b_iters) if b_iters else 0)
        impr_medians.append(np.median(i_iters) if i_iters else 0)

    ax.bar(x - width/2, base_medians, width, label="Baseline", color="#4C72B0")
    ax.bar(x + width/2, impr_medians, width, label="Constraint-Guided", color="#DD8452")
    ax.set_xlabel("Benchmark")
    ax.set_ylabel("Median Iterations to Cover")
    ax.set_title("Constraint-Guided Mutation: Iterations to Cover Target Branch")
    ax.set_xticks(x)
    ax.set_xticklabels(bench_ids, rotation=45, ha="right")
    ax.legend()
    fig.tight_layout()
    fig.savefig(RESULTS_DIR / "bar_chart.png", dpi=150)
    print(f"Bar chart saved to {RESULTS_DIR / 'bar_chart.png'}")

    # --- Box plot ---
    fig2, ax2 = plt.subplots(figsize=(12, 6))
    positions = []
    data_base = []
    data_impr = []
    labels = []
    for idx, bid in enumerate(bench_ids):
        b_iters = [i for i in baseline[bid]["iterations"] if i is not None]
        i_iters = [i for i in improved[bid]["iterations"] if i is not None]
        data_base.append(b_iters if b_iters else [0])
        data_impr.append(i_iters if i_iters else [0])
        labels.append(bid)

    bp1 = ax2.boxplot(data_base, positions=x - 0.2, widths=0.3,
                      patch_artist=True, boxprops=dict(facecolor="#4C72B0", alpha=0.7))
    bp2 = ax2.boxplot(data_impr, positions=x + 0.2, widths=0.3,
                      patch_artist=True, boxprops=dict(facecolor="#DD8452", alpha=0.7))
    ax2.set_xlabel("Benchmark")
    ax2.set_ylabel("Iterations to Cover")
    ax2.set_title("Distribution of Iterations (Baseline vs Constraint-Guided)")
    ax2.set_xticks(x)
    ax2.set_xticklabels(labels, rotation=45, ha="right")
    ax2.legend([bp1["boxes"][0], bp2["boxes"][0]], ["Baseline", "Constraint-Guided"])
    fig2.tight_layout()
    fig2.savefig(RESULTS_DIR / "box_plot.png", dpi=150)
    print(f"Box plot saved to {RESULTS_DIR / 'box_plot.png'}")

    # --- Summary table ---
    print("\n=== Summary ===")
    print(f"{'Benchmark':<20} {'Base Med':>10} {'Impr Med':>10} {'Speedup':>10} {'Base TO':>8} {'Impr TO':>8}")
    print("-" * 70)
    for idx, bid in enumerate(bench_ids):
        b_iters = [i for i in baseline[bid]["iterations"] if i is not None]
        i_iters = [i for i in improved[bid]["iterations"] if i is not None]
        b_med = np.median(b_iters) if b_iters else float("inf")
        i_med = np.median(i_iters) if i_iters else float("inf")
        speedup = b_med / i_med if i_med > 0 else float("inf")
        b_to = len(baseline[bid]["iterations"]) - len(b_iters)
        i_to = len(improved[bid]["iterations"]) - len(i_iters)
        print(f"{bid:<20} {b_med:>10.1f} {i_med:>10.1f} {speedup:>9.2f}x {b_to:>8} {i_to:>8}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Micro-benchmark runner")
    parser.add_argument("command", choices=["baseline", "improved", "compare"])
    parser.add_argument("--trials", type=int, default=10)
    parser.add_argument("--duration", type=int, default=60)
    args = parser.parse_args()

    if args.command == "compare":
        compare()
    else:
        run_benchmarks(args.command, args.trials, args.duration)
