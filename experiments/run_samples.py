#!/usr/bin/env python3
import argparse
import os
import re
import shlex
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Tuple

FILENAME_RE = re.compile(
    r"^(?P<branch>\d+)-(?P<truth>true|false)\.json$", re.IGNORECASE
)
COVERED_RE = re.compile(r"Covered\s+.+?\s+with\s+(?P<iters>\d+)\s+iters", re.IGNORECASE)
TIMEOUT_RE = re.compile(r"(?:java\.util\.concurrent\.)?TimeoutException\b", re.IGNORECASE)
UNEXPECTED_RE = re.compile(r"\[ESMeta v[^\]]+\]\s+Unexpected error occurred", re.IGNORECASE)
ESMETA_HOME = (
    Path(os.getenv("ESMETA_HOME") or Path(__file__).resolve().parent.parent)
    .expanduser()
    .resolve()
)

TRIAL, DURATION = 10, 300


@dataclass
class RunResult:
    file: str
    branch: int
    truth: bool
    run_idx: int
    status: str  # "Covered" | "Timeout" | "Unknown"
    iters: Optional[int]
    last_line: str


def last_nonempty_line(text: str) -> str:
    lines = [ln.rstrip("\n") for ln in text.splitlines()]
    for ln in reversed(lines):
        if ln.strip():
            return ln.strip()
    return ""


def run_once(
    duration: int,
    json_path: Path,
    branch: int,
    truth: bool,
    run_idx: int,
) -> RunResult:
    esmeta_argv = shlex.split(str(ESMETA_HOME / "bin" / "esmeta"))
    argv = esmeta_argv + [
        "mutate",
        "-mutate:mutator=TargetMutator",
        f"-mutate:target-branch-id={branch}",
        f"-mutate:target-cond={'true' if truth else 'false'}",
        f"-mutate:duration={duration}",
        str(json_path),
        "-silent",
    ]

    def _run(argv_list: list[str]) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            argv_list,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            check=False,
            cwd=str(ESMETA_HOME),
            timeout=duration,
        )

    def _coerce_text(x) -> str:
        if x is None:
            return ""
        if isinstance(x, bytes):
            return x.decode("utf-8", errors="replace")
        return str(x)

    try:
        proc = _run(argv)
        out = proc.stdout or ""
    except subprocess.TimeoutExpired as e:
        out = _coerce_text(getattr(e, "stdout", None) or getattr(e, "output", None))
        ll = last_nonempty_line(out)
        return RunResult(
            file=json_path.name,
            branch=branch,
            truth=truth,
            run_idx=run_idx,
            status="Timeout",
            iters=None,
            last_line=ll,
        )
    except OSError:
        shell = os.environ.get("SHELL", "/bin/bash")
        cmd_str = " ".join(shlex.quote(x) for x in argv)
        try:
            proc = _run([shell, "-lc", cmd_str])
            out = proc.stdout or ""
        except subprocess.TimeoutExpired as e:
            out = _coerce_text(getattr(e, "stdout", None) or getattr(e, "output", None))
            ll = last_nonempty_line(out)
            return RunResult(
                file=json_path.name,
                branch=branch,
                truth=truth,
                run_idx=run_idx,
                status="Timeout",
                iters=None,
                last_line=ll,
            )

    ll = last_nonempty_line(out)

    status, iters = "Unknown", None

    m_last = None
    for m in COVERED_RE.finditer(out):
        m_last = m
    if m_last:
        status, iters = "Covered", int(m_last.group("iters"))
    elif TIMEOUT_RE.search(out):
        status, iters = "Timeout", None
    else:
        pass

    return RunResult(
        file=json_path.name,
        branch=branch,
        truth=truth,
        run_idx=run_idx,
        status=status,
        iters=iters,
        last_line=ll,
    )


def run_file(
    duration: int, trial: int, p: Path, branch: int, truth: bool
) -> List[RunResult]:
    results: List[RunResult] = []
    for i in range(1, trial + 1):
        rr = run_once(duration, p, branch, truth, run_idx=i)
        results.append(rr)
        if rr.status == "Timeout":
            break
    return results


def format_iters_list(iters: List[int]) -> str:
    return "[ " + ", ".join(str(x) for x in sorted(iters)) + " ]"


def main() -> None:
    d = (Path(__file__).resolve().parent / "samples")
    files: List[Tuple[Path, int, bool]] = []
    for p in sorted(d.iterdir()):
        m = FILENAME_RE.match(p.name)
        if not m:
            continue
        branch = int(m.group("branch"))
        covered_side = m.group("truth").lower() == "true"
        target_side = not covered_side
        files.append((p, branch, target_side))

    out_path = Path("sample-results")
    out_path.parent.mkdir(parents=True, exist_ok=True)

    with out_path.open("w", encoding="utf-8") as f:
        for i, (p, branch, truth) in enumerate(files):
            label = f"Branch[{branch}]:{'T' if truth else 'F'}"
            results = run_file(DURATION, TRIAL, p, branch, truth)
            saw_timeout = any(r.status == "Timeout" for r in results)
            if saw_timeout:
                f.write(f'{label}: "TIMEOUT"\n')
                f.flush()
            else:
                iters_list = [r.iters for r in results if r.status == "Covered"]
                if iters_list:
                    sorted_iters_list = format_iters_list([int(x) for x in iters_list])
                    f.write(f"{label}: {sorted_iters_list}\n")
                else:
                    f.write(f'{label}: "UNKNOWN"\n')
                f.flush()

            msg = f"[{i}] {label}: "
            if saw_timeout:
                msg += "TIMEOUT"
            else:
                msg += f"{len([r for r in results if r.status == 'Covered'])} covered"
            print(msg)

    print(f"\nDone. Wrote: {out_path.resolve()}")


if __name__ == "__main__":
    raise SystemExit(main())
