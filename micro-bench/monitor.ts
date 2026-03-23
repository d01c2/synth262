#!/usr/bin/env -S deno run --allow-run --allow-read --allow-write --allow-env
/**
 * Monitor unsolved branches: run comparison (no ablation) once per branch.
 *
 * Benchmarks file: ./monitor-benchmarks.jsonl
 *
 * Usage: deno task monitor [options]
 */

import { parseArgs } from "@std/cli/parse-args";
import { dirname, fromFileUrl, join } from "@std/path";

// --- Types ---

interface Benchmark {
  id: string;
  branch: number;
  seed: string;
  func: string;
}

interface BenchmarkResult {
  benchmark: Benchmark;
  iteration: number | null;
}

type Results = Record<string, BenchmarkResult>;

// --- Constants ---

const BENCH_DIR = dirname(fromFileUrl(import.meta.url));
const PROJECT_DIR = join(BENCH_DIR, "..");
const RESULTS_DIR = join(BENCH_DIR, "results");
const BENCHMARKS_FILE = join(BENCH_DIR, "monitor-benchmarks.jsonl");

// --- Core ---

async function loadBenchmarks(): Promise<Benchmark[]> {
  const text = await Deno.readTextFile(BENCHMARKS_FILE);
  return text.split("\n").filter((l) => l.trim()).map((l) => JSON.parse(l));
}

async function runSingle(
  branch: number,
  seed: string,
  trial: number,
  duration?: number,
): Promise<number | null> {
  const durationFlag = duration !== undefined
    ? ` -mutate:duration=${duration}`
    : "";
  const cmdString = `sbt -error "run mutate ${seed} -mutate:branch=${branch}` +
    ` -mutate:trial=${trial}${durationFlag}"`;

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
    if (output.signal !== null || output.code === 143) return null;

    const decoder = new TextDecoder();
    const text = decoder.decode(output.stdout) + decoder.decode(output.stderr);
    const m = text.match(/Covered in (\d+)/);
    return m ? parseInt(m[1]) : null;
  } catch {
    return null;
  }
}

async function runMonitor(
  repeat: number,
  trial: number,
  duration?: number,
): Promise<void> {
  await Deno.mkdir(RESULTS_DIR, { recursive: true });
  const benchmarks = await loadBenchmarks();
  const results: Results = {};
  let passed = 0;
  let failed = 0;

  for (const bench of benchmarks) {
    const bid = bench.id;
    console.log(`\n[${bid}] ${bench.func}`);

    let best: number | null = null;
    for (let r = 1; r <= repeat; r++) {
      const it = await runSingle(bench.branch, bench.seed, trial, duration);
      const status = it !== null ? String(it) : "TIMEOUT";
      console.log(`  Run ${r}/${repeat}: ${status}`);

      if (it !== null && (best === null || it < best)) best = it;

      if (it === null && r === 1) {
        console.log("  Skipping remaining runs (first run TIMEOUT)");
        break;
      }
    }

    if (best !== null) passed++;
    else failed++;

    results[bid] = { benchmark: bench, iteration: best };
  }

  const outfile = join(RESULTS_DIR, "monitor.json");
  await Deno.writeTextFile(outfile, JSON.stringify(results, null, 2));

  console.log(`\n=== Summary ===`);
  console.log(`Total: ${benchmarks.length}`);
  console.log(`Passed: ${passed}`);
  console.log(`Failed: ${failed}`);
  console.log(`\nResults saved to ${outfile}`);
}

// --- CLI ---

const args = parseArgs(Deno.args, {
  boolean: ["help"],
  string: ["repeat", "trial", "duration"],
  default: { repeat: "3", trial: "20" },
  alias: { h: "help" },
});

if (args.help) {
  console.log(
    `Usage: deno task monitor [options]

Runs comparison (no ablation) on monitor-benchmarks.jsonl.

Options:
  --repeat N    repetitions per benchmark (default: 3)
  --trial N     mutation budget per run (default: 20)
  --duration N  optional time limit in seconds
  -h, --help    show help`,
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

await runMonitor(repeat, trial, duration);
