#!/usr/bin/env bash
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
export plutus_benchmark_datadir="$root_dir/plutus-benchmark"
for repetition in 1 2 3; do
  variants=(baseline ra-erased-context)
  if [[ "$repetition" == 2 ]]; then variants=(ra-erased-context baseline); fi
  for variant in "${variants[@]}"; do
    output="$experiment_dir/../results/closure-criterion-$variant-r$repetition"
    taskset -c 15 "$experiment_dir/bin/validation-$variant" --quick -L 0.1 \
      --resamples 1000 --csv "$output.csv" \
      -o "$experiment_dir/logs/closure-criterion-$variant-r$repetition.html" \
      > "$output.log" 2>&1
    echo "Canonical benchmark: round $repetition $variant"
  done
done
