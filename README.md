# Synth262

**Synth262** is a *conformance test synthesis* framework for JavaScript built-in
APIs. Instead of mutating inputs and hoping for new coverage, Synth262 works
**backward from a target specification branch**: it infers the *symbolic
structure type* each input must have to reach the branch, constructs a
JavaScript program from that type, and turns the covering program into a
conformance test by reusing a specification-derived oracle.

The analysis is an abstract interpretation over the mechanized ECMA-262
specification produced by [ESMeta](https://github.com/es-meta/esmeta), whose
control-flow graph provides the coverage targets.

This repository is the research artifact for our paper:

> **Synthesizing JavaScript Conformance Tests by Inferring Structure Types from
> the Specification** (ICSE 2027 submission, under double-blind review).

---

## Claims → Artifact

Each headline result in the paper maps to one command in this artifact.

| Paper item | Claim | How to reproduce |
| --- | --- | --- |
| §II-C, motivating example | A single target branch is solved into a covering JavaScript program | [`synth262 solve`](#single-target-solving) |
| **RQ1 / Fig. 7** | Branch-side coverage of Synth262 vs. Test262 and the mutation fuzzer over the 5,802-branch universe | [`CoverageMiddleTest`](#rq1-specification-coverage-fig-7) → [`venn_branch_coverage.py`](#rq1-specification-coverage-fig-7) |
| **RQ2 / Table IV** | Effect of *result-type-sensitive summaries* on coverage and cost | [`summary_ablation.py`](#rq2-effect-of-result-type-sensitive-summaries-table-iv) |
| **RQ3 / §VI-D** | Synthesized tests uncover engine conformance bugs | [`solver_conformance_check.py`](#rq3-engine-conformance-bugs) |
| **Tables II–III** | How a callee's result is split by downstream branches | [`CallResultSplitTest`](#call-result-split-study-tables-iiiii) |

---

## Installation

### Requirements

- **JDK 17+** (tested on GraalVM / Temurin 21)
- **[sbt](https://www.scala-sbt.org/)** — the Scala build tool (project uses Scala 3.3.6)
- **Python 3.9+** — for the `experiment/*.py` reproduction scripts
- *(RQ3 only)* JavaScript engines installed via **[jsvu](https://github.com/GoogleChromeLabs/jsvu)** under `~/.jsvu/bin`
  (any of `v8`, `jsc`/`javascriptcore`, `graaljs`, `sm`/`spidermonkey`, `xs`, `qjs`/`quickjs`)

### Download

```bash
git clone <this-repo-url> synth262
cd synth262
git submodule update --init
```

The submodules provide the ECMA-262 specification (`ecma262`), the Test262 suite
(`tests/test262`), and the debugger client (`client`).

### Environment setting

Add the following to your `~/.zshrc` (or `~/.bashrc`) and reload the shell:

```bash
# Synth262
export SYNTH262_HOME="<absolute path to this repository>"   # IMPORTANT
export PATH="$SYNTH262_HOME/bin:$PATH"                       # for the `synth262` executable
source $SYNTH262_HOME/.completion                            # for shell auto-completion
```

`SYNTH262_HOME` is required by both the `synth262` command and the test suite.

### Build

```bash
sbt assembly && source .completion
```

This generates the launcher at `bin/synth262`. Verify the installation:

```bash
$ synth262
# Synth262 v0.7.1 - ECMAScript Specification Metalanguage
# ...
# Please type `synth262 help` to see the help message.
```

> [!NOTE]
> The first command that touches the specification (`solve`, `inject`, or any
> test) extracts and compiles the mechanized ECMA-262 model from the `ecma262`
> submodule. This one-time step takes a few minutes; later runs reuse the cache.

---

## Single-target solving

Given a **target branch** in the specification CFG, Synth262 synthesizes a
JavaScript program that drives a built-in down the path reaching it. This is the
core capability behind the motivating example in §II-C.

```bash
synth262 solve -solve:branch=<branch-id>               # solve both branch sides
synth262 solve -solve:branch=<branch-id> -solve:side   # solve the true side only
synth262 solve -solve:branch=<branch-id> -solve:detail # verbose symbolic trace
```

The command runs `extract >> compile >> build-cfg >> solve`, searches every
built-in entry that can reach the branch, and prints a covering program:

```
[solve] Branch[<id>]:T: <synthesized JavaScript program>
```

or `no solution` if no candidate within the enumeration budget (64 per path)
covers the branch within the 10 s per-side time limit.

> Branch ids are the CFG node ids of `Branch` nodes. Every target attempted by
> `CoverageMiddleTest` (below) is logged as `Branch[<id>]:<side>` under
> `logs/solver`, so that log is a convenient source of solvable ids.

---

## Reproducing the paper

All coverage results use a single universe: the **5,802** specification
branch sides reachable from the **358** built-in entry algorithms.

### RQ1: Specification coverage (Fig. 7)

**Step 1 — solve every reachable target.** This attempts, for every target
branch reachable from every built-in entry, to synthesize a covering program,
and records the outcome under `logs/solver` (`summary`, `pass`,
`solved-programs`).

```bash
sbt "testOnly synth262.solver.CoverageMiddleTest"
```

**Step 2 — draw the Venn diagram.** This overlaps the solver-covered set
(`logs/solver`) with the Test262 and 50 h-fuzzer coverage archives shipped under
`experiment/data/`.

```bash
python3 experiment/venn_branch_coverage.py
```

Outputs `experiment/result.svg` (Fig. 7) and `experiment/result.json`. Expected
figures: universe **5,802**, Synth262 **2,786 (48.0%)**, Test262 **4,409**,
Fuzz **4,058**, and **35** branch sides covered by Synth262 alone.

### RQ2: Effect of result-type-sensitive summaries (Table IV)

Runs `CoverageMiddleTest` under three summarization modes — *sensitive*
(Synth262), *result-type-insensitive*, and *no summary* — all under the shared
300 s cap, and writes the comparison table.

```bash
python3 experiment/summary_ablation.py
```

Outputs `experiment/ablation.csv` (and `ablation.raw.csv`). Expected coverage:
(a) sensitive **2,786 (48.0%)**, (b) insensitive **2,345 (40.4%)**, (c) no
summary **278 (4.8%)**.

> [!NOTE]
> This runs the full solver three times; the *no-summary* mode intentionally
> hits the per-side timeout on most branches, so this reproduction is the
> slowest.

### RQ3: Engine conformance bugs

**Prerequisites:** a completed solver run (`logs/solver/solved-programs` from
RQ1 Step 1) and JS engines installed via `jsvu`.

```bash
python3 experiment/solver_conformance_check.py
```

This injects final-state assertions into the solved programs using the JEST
injector (`synth262 inject`), runs each injected test on every installed engine,
and records divergences from the specification-derived oracle.

Outputs `experiment/bugs.json` and a per-engine bug count. In the paper this
surfaces **2** previously unknown conformance bugs (one each in QuickJS and
Moddable XS). Missing engines are reported and skipped.

### Call-result split study (Tables II–III)

Justifies the *result-type-sensitive* summary design by measuring, across the
specification, how each call's result is consumed and split by downstream
branches.

```bash
sbt "testOnly synth262.solver.CallResultSplitTest"
```

Reproduces the distributions behind **Table II** (how the result of each of
8,870 call sites is used) and **Table III** (the target-type splits at the 3,359
sites that branch on a call result).

---

## Repository layout

```
src/main/scala/synth262/          # framework sources (an ESMeta-based toolchain)
  solver/SymInterp.scala          #   symbolic interpreter
  solver/Solver.scala             #   structure-type solver & program synthesis
  phase/Solve.scala               #   `solve` command entry point
  injector/                       #   JEST final-state assertion injector (RQ3)
  extractor/ compiler/ cfgbuilder/#   ECMA-262 -> IR -> CFG mechanization (from ESMeta)
  ir/ ty/ cfg/ es/ state/ ...     #   supporting packages
src/test/scala/synth262/solver/
  CoverageMiddleTest.scala        # RQ1/RQ2 driver: solve all reachable targets
  CallResultSplitTest.scala       # Tables II-III: call-result usage study
experiment/
  venn_branch_coverage.py         # RQ1 / Fig. 7   -> result.svg, result.json
  summary_ablation.py             # RQ2 / Table IV -> ablation.csv
  solver_conformance_check.py     # RQ3            -> bugs.json
  data/                           # pre-collected Test262 + 50 h-fuzz coverage archives
ecma262/  tests/test262/  client/ # git submodules
logs/                             # generated run outputs (git-ignored)
```
