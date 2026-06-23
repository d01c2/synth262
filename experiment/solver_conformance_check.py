#!/usr/bin/env python3
import json, os, re, subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "logs" / "solver" / "solved-programs"
INJECTED = ROOT / "logs" / "solver" / "injected"
REPORT = ROOT / "experiment" / "bugs.json"
TIMEOUT = 10
JOBS = os.cpu_count() or 1
JSVU = Path.home() / ".jsvu" / "bin"

ENGINES = {
    "v8": ("v8",),
    "javascriptcore": ("jsc", "javascriptcore"),
    "graaljs": ("graaljs",),
    "spidermonkey": ("sm", "spidermonkey"),
    "xs": ("xs",),
    "quickjs": ("qjs", "quickjs"),
}
EXIT = re.compile(r"//\s*\[EXIT\]\s*(normal|throw|timeout)")
UNHANDLED = re.compile(r"unhandled.{0,30}(reject|promise)", re.I)
DELAY_CALL = re.compile(r"^\s*\$delay\s*\(", re.M)


def inject():
    env = {**os.environ, "ESMETA_HOME": str(ROOT)}
    cmd = f"run inject {INPUT} -inject:batch -inject:defs -inject:out={INJECTED}"
    subprocess.run(["sbt", cmd], cwd=ROOT, env=env, check=True)
    return sorted(INJECTED.glob("*.js"))


def engine_bins():
    found = {}
    for name in ENGINES:
        found[name] = next((JSVU / alias for alias in ENGINES[name] if (JSVU / alias).exists()), None)
    return {k: v for k, v in found.items() if v}, [k for k, v in found.items() if not v]


def program_of(code):
    lines = []
    for line in code.splitlines():
        if line == "// Assertions":
            break
        if line == '"use strict";' or line.startswith("// [EXIT]"):
            continue
        lines.append(line)
    return "\n".join(lines).strip()


def check(engine, path):
    code = path.read_text(errors="replace")
    match = EXIT.search(code)
    want = match.group(1) if match else "normal"
    delayed = DELAY_CALL.search(code)
    try:
        p = subprocess.run([str(engine), str(path)], cwd=ROOT, capture_output=True, text=True, timeout=TIMEOUT)
        out, err = p.stdout.strip(), p.stderr.strip()
        got = "normal" if p.returncode == 0 else "throw"
    except subprocess.TimeoutExpired:
        got, out, err = "timeout", "", ""

    category = (
        "host-unhandled-rejection"
        if UNHANDLED.search(out + "\n" + err)
        else "exit-tag-mismatch"
        if got != want
        else "async-assertion-fail"
        if delayed and want == "normal" and out
        else "assertion-fail"
        if want == "normal" and out
        else None
    )
    if category is None:
        return "pass", None

    rec = {
        "program": program_of(code),
        "category": category,
        "expected": want,
        "concrete": got,
    }
    for key, text in (("stdout", out), ("stderr", err)):
        if text:
            rec[key] = text[:1000] + ("..." if len(text) > 1000 else "")
    return ("skip" if category.startswith("host-") else "fail"), rec


def group_bugs(records):
    bugs = {}
    for rec in records:
        bug = bugs.setdefault(rec["program"], {"program": rec["program"], "failures": {}})
        key = tuple(rec.get(k, "") for k in ("category", "expected", "concrete", "stdout", "stderr"))
        failure = bug["failures"].setdefault(
            key,
            {k: rec[k] for k in ("category", "expected", "concrete") if k in rec},
        )
        for k in ("stdout", "stderr"):
            if k in rec:
                failure[k] = rec[k]

    return [
        {**bug, "failures": list(bug["failures"].values())}
        for bug in sorted(bugs.values(), key=lambda x: x["program"])
    ]


def run_engine(engine, tests):
    with ThreadPoolExecutor(max_workers=JOBS) as pool:
        records = list(pool.map(lambda path: check(engine, path), tests))
    return group_bugs([rec for kind, rec in records if kind == "fail"])


def main():
    if not INPUT.exists():
        raise SystemExit(f"not found: {INPUT}")
    tests = inject()
    if not tests:
        raise SystemExit(f"no injected .js files in {INJECTED}")

    bins, missing = engine_bins()
    if missing:
        print("not installed:", ", ".join(missing))
    if not bins:
        raise SystemExit(f"no engines found in {JSVU}")

    results = {name: {"engine": str(bin), "bugs": run_engine(bin, tests)} for name, bin in bins.items()}
    REPORT.parent.mkdir(parents=True, exist_ok=True)
    REPORT.write_text(json.dumps({"input": str(INPUT), "injected": str(INJECTED), "engines": results}, indent=2) + "\n")

    print(f"{'engine':<14}{'bugs':>7}")
    for name, summary in results.items():
        print(f"{name:<14}{len(summary['bugs']):>7}")
    print(f"\n{REPORT}")


if __name__ == "__main__":
    main()
