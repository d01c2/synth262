#!/usr/bin/env python3
"""Run solver may/must ablation modes and write a CSV summary."""

from __future__ import annotations

import argparse
import csv
import re
import subprocess
import sys
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TEST_TASK = "Test / testOnly esmeta.solver.CoverageMiddleTest"
DEFAULT_OUTPUT = ROOT / "experiment" / "ablation.csv"
DEFAULT_REPEAT = 10

MODES = [
    ("default", ["sbt", TEST_TASK]),
    ("must-only", ["sbt", "-Desmeta.solver.useMay=false", TEST_TASK]),
    ("may-only", ["sbt", "-Desmeta.solver.useMust=false", TEST_TASK]),
]

PASS_RE = re.compile(r"^\s*pass\s+(\d+)\s+\(\s*([0-9.]+)%\)")
TOTAL_RE = re.compile(r"^\s*total\s+(\d+)\s+\(100\.0%\)")


def parse_coverage(output: str) -> tuple[int | None, int | None, float | None]:
    passed = None
    percent = None
    total = None
    for line in output.splitlines():
        if match := PASS_RE.match(line):
            passed = int(match.group(1))
            percent = float(match.group(2))
        elif match := TOTAL_RE.match(line):
            total = int(match.group(1))
    return passed, total, percent


def run_mode(mode: str, run: int, command: list[str]) -> dict[str, str]:
    start = time.perf_counter()
    output_lines: list[str] = []
    process = subprocess.Popen(
        command,
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        bufsize=1,
    )
    assert process.stdout is not None
    for line in process.stdout:
        print(line, end="")
        output_lines.append(line)
    code = process.wait()
    elapsed = time.perf_counter() - start
    output = "".join(output_lines)
    passed, total, percent = parse_coverage(output)
    status = "pass" if code == 0 else "failed"
    return {
        "mode": mode,
        "run": str(run),
        "status": status,
        "coverage_pass": "" if passed is None else str(passed),
        "coverage_total": "" if total is None else str(total),
        "coverage_percent": "" if percent is None else f"{percent:.1f}",
        "elapsed": f"{elapsed:.2f}",
    }


def mean(values: list[float]) -> float:
    return sum(values) / len(values)


def summarize(raw_rows: list[dict[str, str]]) -> list[dict[str, str]]:
    rows = []
    for mode, _ in MODES:
        mode_rows = [row for row in raw_rows if row["mode"] == mode]
        ok_rows = [row for row in mode_rows if row["status"] == "pass"]
        pass_counts = [
            float(row["coverage_pass"])
            for row in ok_rows
            if row["coverage_pass"]
        ]
        percents = [
            float(row["coverage_percent"])
            for row in ok_rows
            if row["coverage_percent"]
        ]
        elapsed = [float(row["elapsed"]) for row in ok_rows]
        if ok_rows:
            coverage_mean = mean(pass_counts) if pass_counts else 0.0
            percent_mean = mean(percents) if percents else 0.0
            elapsed_mean = mean(elapsed)
            rows.append({
                "mode": mode,
                "coverage": f"{coverage_mean:.1f} ({percent_mean:.1f}%)",
                "elapsed": f"{elapsed_mean:.2f}",
            })
        else:
            rows.append({
                "mode": mode,
                "coverage": "failed",
                "elapsed": "",
            })
    return rows


def write_csv(path: Path, fieldnames: list[str], rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Run solver may/must ablation modes and write mode,coverage,elapsed CSV.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"CSV output path. Default: {DEFAULT_OUTPUT}",
    )
    parser.add_argument(
        "--repeat",
        type=int,
        default=DEFAULT_REPEAT,
        help=f"Runs per mode. Default: {DEFAULT_REPEAT}",
    )
    args = parser.parse_args()

    if args.repeat <= 0:
        raise ValueError("--repeat must be positive")

    raw_output = args.output.with_suffix(".raw.csv")
    raw_rows: list[dict[str, str]] = []
    failed = False
    for mode, command in MODES:
        for run in range(1, args.repeat + 1):
            print(f"\n=== {mode} run {run}/{args.repeat}: {' '.join(command)} ===")
            row = run_mode(mode, run, command)
            raw_rows.append(row)
            failed = failed or row["status"] != "pass"
            write_csv(
                raw_output,
                [
                    "mode",
                    "run",
                    "status",
                    "coverage_pass",
                    "coverage_total",
                    "coverage_percent",
                    "elapsed",
                ],
                raw_rows,
            )
            write_csv(
                args.output,
                ["mode", "coverage", "elapsed"],
                summarize(raw_rows),
            )

    print(f"\nCSV written to {args.output}")
    print(f"Raw CSV written to {raw_output}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
