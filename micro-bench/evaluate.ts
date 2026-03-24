#!/usr/bin/env -S deno run --allow-run --allow-read --allow-write --allow-env --allow-ffi
/**
 * micro-bench evaluation: baseline -> comparison -> compare.
 *
 * Usage: deno run --allow-run --allow-read --allow-write --allow-env --allow-ffi evaluate.ts [options]
 */

import { parseArgs } from "@std/cli/parse-args";
import { dirname, fromFileUrl, join } from "@std/path";
import chalk from "chalk";

// --- Types ---

interface Benchmark {
  id: string;
  branch: number;
  seed: string;
  func: string;
}

interface BenchmarkResult {
  benchmark: Benchmark;
  iterations: (number | null)[];
  timestamp: string;
}

type Results = Record<string, BenchmarkResult>;

// --- Constants ---

const BENCH_DIR = dirname(fromFileUrl(import.meta.url));
const PROJECT_DIR = join(BENCH_DIR, "..");
const RESULTS_DIR = join(BENCH_DIR, "results");
const BENCHMARKS_FILE = join(BENCH_DIR, "benchmarks.jsonl");

// --- Core Functions ---

async function loadBenchmarks(): Promise<Benchmark[]> {
  const text = await Deno.readTextFile(BENCHMARKS_FILE);
  return text.split("\n").filter((line) => line.trim()).map((line) =>
    JSON.parse(line)
  );
}

async function runSingle(
  branch: number,
  seed: string,
  trial: number,
  duration?: number,
  ablation = false,
): Promise<number | null> {
  const ablationFlag = ablation ? " -mutate:ablation" : "";
  const durationFlag = duration !== undefined
    ? ` -mutate:duration=${duration}`
    : "";
  const cmdString = `sbt -error "run mutate ${seed} -mutate:branch=${branch}` +
    ` -mutate:trial=${trial}${durationFlag}${ablationFlag}"`;

  const procTimeout = duration !== undefined
    ? duration + 60
    : Math.max(Math.floor(trial / 2), 300);

  try {
    const cmd = new Deno.Command("sh", {
      args: ["-c", cmdString],
      cwd: PROJECT_DIR,
      stdout: "piped",
      stderr: "piped",
      signal: AbortSignal.timeout(procTimeout * 1000),
    });

    const output = await cmd.output();

    // Defensive: check for killed-by-signal in case timeout doesn't throw
    if (output.signal !== null || output.code === 143) return null;

    const decoder = new TextDecoder();
    const text = decoder.decode(output.stdout) + decoder.decode(output.stderr);
    const m = text.match(/Covered in (\d+)/);
    return m ? parseInt(m[1]) : null;
  } catch {
    // AbortSignal.timeout() throws DOMException on expiry
    return null;
  }
}

async function runBenchmarks(
  label: string,
  repeat: number,
  trial: number,
  duration?: number,
): Promise<void> {
  await Deno.mkdir(RESULTS_DIR, { recursive: true });
  const benchmarks = await loadBenchmarks();
  const results: Results = {};
  const ablation = label === "baseline";

  for (const bench of benchmarks) {
    const bid = bench.id;
    console.log(`\n[${bid}]`);
    const iterations: (number | null)[] = [];

    for (let r = 1; r <= repeat; r++) {
      const it = await runSingle(
        bench.branch,
        bench.seed,
        trial,
        duration,
        ablation,
      );
      const status = it !== null ? String(it) : "TIMEOUT";
      console.log(`  Run ${r}/${repeat}: ${status}`);
      iterations.push(it);

      // Only skip remaining runs when run #1 times out.
      // Later timeouts record null but continue remaining runs.
      if (it === null && r === 1) {
        console.log("  Skipping remaining runs (first run TIMEOUT)");
        break;
      }
    }

    results[bid] = {
      benchmark: bench,
      iterations,
      timestamp: new Date().toISOString(),
    };
  }

  const outfile = join(RESULTS_DIR, `${label}.json`);
  await Deno.writeTextFile(outfile, JSON.stringify(results, null, 2));
  console.log(`\nResults saved to ${outfile}`);
}

// --- Visualization Helpers ---

function filterIters(raw: (number | null)[]): [number[], number] {
  const ok = raw.filter((i): i is number => i !== null);
  return [ok, raw.length - ok.length];
}

function calcQuartiles(data: number[]): {
  min: number;
  q1: number;
  median: number;
  q3: number;
  max: number;
} {
  const sorted = [...data].sort((a, b) => a - b);
  const n = sorted.length;
  if (n === 0) return { min: 0, q1: 0, median: 0, q3: 0, max: 0 };
  if (n === 1) {
    return {
      min: sorted[0],
      q1: sorted[0],
      median: sorted[0],
      q3: sorted[0],
      max: sorted[0],
    };
  }

  const percentile = (p: number): number => {
    const idx = (p / 100) * (n - 1);
    const lo = Math.floor(idx);
    const hi = Math.ceil(idx);
    return lo === hi
      ? sorted[lo]
      : sorted[lo] + (sorted[hi] - sorted[lo]) * (idx - lo);
  };

  return {
    min: sorted[0],
    q1: percentile(25),
    median: percentile(50),
    q3: percentile(75),
    max: sorted[n - 1],
  };
}

function renderAsciiBoxPlot(
  data: number[],
  label: string,
  globalMin: number,
  globalMax: number,
  colorFn: (s: string) => string,
  width = 50,
): string {
  if (data.length === 0) {
    return `  ${label.padEnd(12)} ${colorFn("TIMEOUT")}`;
  }

  const q = calcQuartiles(data);
  const range = globalMax - globalMin || 1;

  const scale = (v: number) =>
    Math.min(width, Math.max(0, Math.round(((v - globalMin) / range) * width)));

  const minPos = scale(q.min);
  const q1Pos = scale(q.q1);
  const medPos = scale(q.median);
  const q3Pos = scale(q.q3);
  const maxPos = scale(q.max);

  const line = new Array(width + 1).fill(" ");

  // Whiskers
  for (let i = minPos; i <= q1Pos; i++) line[i] = "-";
  for (let i = q3Pos; i <= maxPos; i++) line[i] = "-";

  // Box
  for (let i = q1Pos; i <= q3Pos; i++) line[i] = "=";
  line[q1Pos] = "[";
  line[q3Pos] = "]";

  // Median
  line[medPos] = "|";

  // Endpoints (only when they don't coincide with brackets)
  if (minPos !== q1Pos) line[minPos] = "\u00B7"; // ·
  if (maxPos !== q3Pos) line[maxPos] = "\u00B7"; // ·

  return `  ${label.padEnd(12)} ${colorFn(line.join(""))}`;
}

// --- Compare ---

async function compare(): Promise<void> {
  const baselineFile = join(RESULTS_DIR, "baseline.json");
  const comparisonFile = join(RESULTS_DIR, "comparison.json");

  for (const f of [baselineFile, comparisonFile]) {
    try {
      await Deno.stat(f);
    } catch {
      console.log(`Missing ${f}. Run evaluate.ts first.`);
      Deno.exit(1);
    }
  }

  const baseline: Results = JSON.parse(
    await Deno.readTextFile(baselineFile),
  );
  const comparison: Results = JSON.parse(
    await Deno.readTextFile(comparisonFile),
  );

  const benchIds = Object.keys(baseline)
    .filter((id) => id in comparison)
    .sort();

  // --- ASCII Box Plots ---
  console.log("\n" + chalk.bold("[ASCII Box Plots]"));
  for (const bid of benchIds) {
    const [bOk] = filterIters(baseline[bid].iterations);
    const [cOk] = filterIters(comparison[bid].iterations);
    const allValues = [...bOk, ...cOk];
    const globalMin = allValues.length > 0 ? Math.min(...allValues) : 0;
    const globalMax = allValues.length > 0 ? Math.max(...allValues) : 1;

    console.log(`  ${chalk.bold(bid)}`);
    console.log(
      renderAsciiBoxPlot(bOk, "Baseline", globalMin, globalMax, chalk.blue),
    );
    console.log(
      renderAsciiBoxPlot(
        cOk,
        "Comparison",
        globalMin,
        globalMax,
        (s: string) => chalk.hex("#DD8452")(s),
      ),
    );
  }

  // --- Colored Summary Table ---
  console.log("\n" + chalk.bold("[Summary]"));
  const header = `${"Benchmark".padEnd(20)} ${"Base Avg".padStart(10)} ${
    "Comp Avg".padStart(10)
  } ${"Speedup".padStart(10)} ${"Base TO".padStart(8)} ${
    "Comp TO".padStart(8)
  }`;
  console.log(chalk.bold(header));
  console.log("-".repeat(header.length));

  for (const bid of benchIds) {
    const [bOk, bTo] = filterIters(baseline[bid].iterations);
    const [cOk, cTo] = filterIters(comparison[bid].iterations);
    const bAvg = bOk.length > 0
      ? bOk.reduce((a, b) => a + b, 0) / bOk.length
      : Infinity;
    const cAvg = cOk.length > 0
      ? cOk.reduce((a, b) => a + b, 0) / cOk.length
      : Infinity;
    const speedup = isFinite(bAvg) && isFinite(cAvg) && cAvg > 0
      ? bAvg / cAvg
      : Infinity;

    const bAvgStr = isFinite(bAvg) ? bAvg.toFixed(1) : "Inf";
    const cAvgStr = isFinite(cAvg) ? cAvg.toFixed(1) : "Inf";
    const speedupStr = isFinite(speedup) ? `${speedup.toFixed(2)}x` : "Inf";

    const colorSpeedup = speedup > 1.0
      ? chalk.green
      : speedup < 1.0
      ? chalk.red
      : chalk.yellow;
    const fmtTo = (n: number) =>
      n > 0 ? chalk.gray(String(n).padStart(8)) : String(n).padStart(8);

    console.log(
      `${bid.padEnd(20)} ${bAvgStr.padStart(10)} ${cAvgStr.padStart(10)} ${
        colorSpeedup(speedupStr.padStart(10))
      } ${fmtTo(bTo)} ${fmtTo(cTo)}`,
    );
  }

  // --- PNG Box Plot via Vega-Lite ---
  const chartData: Array<{
    benchmark: string;
    iterations: number;
    group: string;
  }> = [];
  const toAnnotations: Array<{
    benchmark: string;
    group: string;
    label: string;
  }> = [];

  for (const bid of benchIds) {
    const [bOk, bTo] = filterIters(baseline[bid].iterations);
    const [cOk, cTo] = filterIters(comparison[bid].iterations);
    for (const v of bOk) {
      chartData.push({ benchmark: bid, iterations: v, group: "Baseline" });
    }
    for (const v of cOk) {
      chartData.push({ benchmark: bid, iterations: v, group: "Comparison" });
    }
    // Collect timeout annotations
    if (bTo > 0) {
      toAnnotations.push({
        benchmark: bid,
        group: "Baseline",
        label: `TO(${bTo})`,
      });
    }
    if (cTo > 0) {
      toAnnotations.push({
        benchmark: bid,
        group: "Comparison",
        label: `TO(${cTo})`,
      });
    }
  }

  {
    // Dynamic imports — heavy deps only loaded when actually generating PNG
    const vega = await import("vega");
    const vegaLite = await import("vega-lite");
    const { Resvg } = await import("@resvg/resvg-js");

    const colors = {
      domain: ["Baseline", "Comparison"],
      range: ["#85B7EB", "#F0997B"],
    };

    // deno-lint-ignore no-explicit-any
    const layers: any[] = [];

    // Box plot layer (only if we have data)
    if (chartData.length > 0) {
      layers.push({
        data: { values: chartData },
        mark: { type: "boxplot", extent: 1.5, size: 30 },
        encoding: {
          x: { field: "benchmark", type: "nominal", title: "Benchmark" },
          y: {
            field: "iterations",
            type: "quantitative",
            title: "Iterations to Cover",
          },
          color: {
            field: "group",
            type: "nominal",
            scale: colors,
            title: "Group",
          },
          xOffset: { field: "group" },
        },
      });
    }

    // Timeout annotation layer — red "TO" markers near the bottom of the plot
    if (toAnnotations.length > 0) {
      layers.push({
        data: { values: toAnnotations },
        mark: {
          type: "text",
          fontSize: 10,
          fontWeight: "bold",
          baseline: "bottom",
          dy: -4,
          color: "black",
        },
        encoding: {
          x: { field: "benchmark", type: "nominal" },
          y: { datum: 0 },
          text: { field: "label", type: "nominal" },
          xOffset: { field: "group" },
        },
      });
    }

    const spec = {
      $schema: "https://vega.github.io/schema/vega-lite/v5.json",
      width: 800,
      height: 400,
      title: "Distribution of Iterations (Baseline vs Comparison)",
      layer: layers,
    };

    // deno-lint-ignore no-explicit-any
    const vegaSpec = vegaLite.compile(spec as any).spec;
    const view = new vega.View(vega.parse(vegaSpec), { renderer: "none" });
    const svg = await view.toSVG();
    const resvg = new Resvg(svg, {
      fitTo: { mode: "width" as const, value: 1800 },
    });
    const png = resvg.render().asPng();
    await Deno.writeFile(join(RESULTS_DIR, "box_plot.png"), png);
    console.log(`\nBox plot saved to ${join(RESULTS_DIR, "box_plot.png")}`);
  }
}

// --- CLI Entry Point ---

const args = parseArgs(Deno.args, {
  boolean: ["help"],
  string: ["repeat", "trial", "duration"],
  default: { repeat: "3", trial: "20" },
  alias: { h: "help" },
});

if (args.help) {
  console.log(
    `Usage: deno run --allow-run --allow-read --allow-write --allow-env --allow-ffi evaluate.ts [options]

Options:
  --repeat N    number of repetitions per benchmark (default: 3)
  --trial N     mutation budget per run (default: 20)
  --duration N  optional time limit in seconds
  -h, --help    show this help message`,
  );
  Deno.exit(0);
}

const repeat = parseInt(args.repeat as string);
const trial = parseInt(args.trial as string);
const duration = args.duration ? parseInt(args.duration as string) : undefined;

if (isNaN(repeat) || repeat < 1) {
  console.error("--repeat must be a positive integer");
  Deno.exit(1);
}
if (isNaN(trial) || trial < 1) {
  console.error("--trial must be a positive integer");
  Deno.exit(1);
}
if (duration !== undefined && (isNaN(duration) || duration < 1)) {
  console.error("--duration must be a positive integer");
  Deno.exit(1);
}

await runBenchmarks("baseline", repeat, trial, duration);
await runBenchmarks("comparison", repeat, trial, duration);
await compare();
