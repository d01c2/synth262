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

MODES = [
    ("default", ["sbt", TEST_TASK]),
    ("must-only", ["sbt", "-Desmeta.solver.useMay=false", TEST_TASK]),
    ("may-only", ["sbt", "-Desmeta.solver.useMust=false", TEST_TASK]),
]

PASS_RE = re.compile(r"^\s*pass\s+(\d+)\s+\(\s*([0-9.]+)%\)")
TOTAL_RE = re.compile(r"^\s*total\s+(\d+)\s+\(100\.0%\)")


def parse_coverage(output: str) -> str:
    passed = None
    percent = None
    total = None
    for line in output.splitlines():
        if match := PASS_RE.match(line):
            passed = int(match.group(1))
            percent = match.group(2)
        elif match := TOTAL_RE.match(line):
            total = int(match.group(1))
    if passed is None or percent is None:
        return "unknown"
    if total is None:
        return f"{passed} ({percent}%)"
    return f"{passed}/{total} ({percent}%)"


def run_mode(mode: str, command: list[str]) -> dict[str, str]:
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
    coverage = parse_coverage(output)
    if code != 0:
        coverage = "failed" if coverage == "unknown" else f"failed; {coverage}"
    return {
        "mode": mode,
        "coverage": coverage,
        "elapsed": f"{elapsed:.2f}",
    }


def write_csv(path: Path, rows: list[dict[str, str]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as file:
        writer = csv.DictWriter(file, fieldnames=["mode", "coverage", "elapsed"])
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
    args = parser.parse_args()

    rows: list[dict[str, str]] = []
    failed = False
    for mode, command in MODES:
        print(f"\n=== {mode}: {' '.join(command)} ===")
        row = run_mode(mode, command)
        rows.append(row)
        write_csv(args.output, rows)
        failed = failed or row["coverage"].startswith("failed")

    print(f"\nCSV written to {args.output}")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
