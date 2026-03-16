#!/bin/bash
# Usage: ./bench.sh <branch_id> <seed_file> <n_trials> [duration_per_trial] [--ablation]
set -euo pipefail

BRANCH=$1
SEED=$2
N=${3:-10}
DUR=${4:-60}
ABLATION=""
if [[ "${5:-}" == "--ablation" ]]; then
  ABLATION=" -mutate:ablation"
fi

echo "=== Benchmark: branch=$BRANCH seed=$SEED trials=$N duration=${DUR}s ablation=${ABLATION:+on}${ABLATION:-off} ==="

RESULTS=()
for i in $(seq 1 "$N"); do
  ITER=$(cd "$(dirname "$0")/.." && sbt -error "run mutate $SEED -mutate:branch=$BRANCH -mutate:duration=$DUR$ABLATION" 2>&1 \
    | grep -oP 'Covered in \K[0-9]+' || echo "TIMEOUT")
  RESULTS+=("$ITER")
  echo "  Trial $i: $ITER"
done

echo "--- Results: ${RESULTS[*]} ---"
