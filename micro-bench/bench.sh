#!/bin/bash
# Usage: ./bench.sh <branch_id> <seed_file> <n_trials> [duration_per_trial]
set -euo pipefail

BRANCH=$1
SEED=$2
N=${3:-10}
DUR=${4:-60}

echo "=== Benchmark: branch=$BRANCH seed=$SEED trials=$N duration=${DUR}s ==="

RESULTS=()
for i in $(seq 1 "$N"); do
  ITER=$(cd "$(dirname "$0")/.." && sbt -error "run mutate $SEED -mutate:branch=$BRANCH -mutate:duration=$DUR" 2>&1 \
    | grep -oP 'Covered in \K[0-9]+' || echo "TIMEOUT")
  RESULTS+=("$ITER")
  echo "  Trial $i: $ITER"
done

echo "--- Results: ${RESULTS[*]} ---"
