#!/usr/bin/env python3
"""Run CoverageMiddleTest ablations and summarize solver coverage results."""

from __future__ import annotations

import csv
import os
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SUMMARY = ROOT / "logs" / "solver" / "summary"
OUT = ROOT / "experiment" / "ablation.csv"
RAW_OUT = ROOT / "experiment" / "ablation.raw.csv"
TEST_TASK = "Test / testOnly synth262.solver.CoverageMiddleTest"
TOTAL_TIMEOUT_S = 300  # timeout: 300 sec (5 min)

MODES = [
    ("baseline", False, False),
    ("result-type-insensitive", True, False),
    ("no-summary", False, True),
]

STATUS_RE = re.compile(
    r"^\s+(?P<status>[a-z-]+)\s+"
    r"(?P<count>\d+)\s+"
    r"\(\s*(?P<pct>[0-9.]+)%\)\s+"
    r"\(total\s+(?P<total_s>[0-9.]+)s"
    r"(?:,\s+avg\s+(?P<avg_s>[0-9.]+)s)?"
    r",\s+avg attempts\s+(?P<avg_attempts>[0-9.]+)\)",
)


def run_test(mode: str, result_type_insensitive: bool, no_summary: bool) -> None:
    env = {
        **os.environ,
        "SYNTH262_HOME": str(ROOT),
        "SYNTH262_COVERAGE_RESULT_TYPE_INSENSITIVE": (
            "true" if result_type_insensitive else "false"
        ),
        "SYNTH262_COVERAGE_NO_SUMMARY": "true" if no_summary else "false",
        "SYNTH262_COVERAGE_TOTAL_TIMEOUT": str(TOTAL_TIMEOUT_S),
    }
    print(f"==> {mode}")
    subprocess.run(["sbt", TEST_TASK], cwd=ROOT, env=env, check=True)


def parse_summary(
    mode: str,
    result_type_insensitive: bool,
    no_summary: bool,
) -> list[dict[str, str]]:
    if not SUMMARY.exists():
        raise FileNotFoundError(f"summary not found: {SUMMARY}")

    rows: list[dict[str, str]] = []
    for line in SUMMARY.read_text(encoding="utf-8").splitlines():
        match = STATUS_RE.match(line)
        if not match:
            continue
        row = match.groupdict(default="")
        row["mode"] = mode
        row["result_type_insensitive"] = str(result_type_insensitive).lower()
        row["no_summary"] = str(no_summary).lower()
        rows.append(row)

    if not rows:
        raise ValueError(f"no status breakdown rows found in {SUMMARY}")
    return rows


def compact_row(
    mode: str,
    result_type_insensitive: bool,
    no_summary: bool,
    rows: list[dict[str, str]],
) -> dict[str, str]:
    by_status = {row["status"]: row for row in rows}

    def count(status: str) -> int:
        return int(by_status.get(status, {}).get("count", "0") or "0")

    total = count("total")
    passed = count("pass")
    fail_verify = count("fail-verify")
    solved = passed + fail_verify
    total_time_s = by_status.get("total", {}).get("total_s", "")
    avg_attempts = by_status.get("total", {}).get("avg_attempts", "")
    pass_rate = f"{passed / total:.6f}" if total else ""
    solved_rate = f"{solved / total:.6f}" if total else ""

    return {
        "mode": mode,
        "result_type_insensitive": str(result_type_insensitive).lower(),
        "no_summary": str(no_summary).lower(),
        "total": str(total),
        "pass": str(passed),
        "fail_verify": str(fail_verify),
        "fail_reify": str(count("fail-reify")),
        "unsolved": str(count("unsolved")),
        "timeout": str(count("timeout")),
        "not_run": str(count("not-run")),
        "solved": str(solved),
        "pass_rate": pass_rate,
        "solved_rate": solved_rate,
        "total_time_s": total_time_s,
        "avg_attempts": avg_attempts,
    }


def write_csv(path: Path, rows: list[dict[str, str]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fields)
        writer.writeheader()
        writer.writerows(rows)


def main() -> int:
    raw_rows: list[dict[str, str]] = []
    summary_rows: list[dict[str, str]] = []

    for mode, result_type_insensitive, no_summary in MODES:
        run_test(mode, result_type_insensitive, no_summary)
        rows = parse_summary(mode, result_type_insensitive, no_summary)
        raw_rows.extend(rows)
        summary_rows.append(
            compact_row(mode, result_type_insensitive, no_summary, rows),
        )

    write_csv(
        RAW_OUT,
        raw_rows,
        [
            "mode",
            "result_type_insensitive",
            "no_summary",
            "status",
            "count",
            "pct",
            "total_s",
            "avg_s",
            "avg_attempts",
        ],
    )
    write_csv(
        OUT,
        summary_rows,
        [
            "mode",
            "result_type_insensitive",
            "no_summary",
            "total",
            "pass",
            "fail_verify",
            "fail_reify",
            "unsolved",
            "timeout",
            "not_run",
            "solved",
            "pass_rate",
            "solved_rate",
            "total_time_s",
            "avg_attempts",
        ],
    )

    print(f"\nwrote {OUT}")
    print(f"wrote {RAW_OUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
