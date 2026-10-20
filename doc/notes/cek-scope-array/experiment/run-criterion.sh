#!/usr/bin/env bash
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
export plutus_benchmark_datadir="$root_dir/plutus-benchmark"
for repetition in 1 2 3; do
  variants=(baseline compact-checked)
  if [[ "$repetition" == 2 ]]; then variants=(compact-checked baseline); fi
  for variant in "${variants[@]}"; do
    output="$experiment_dir/../results/criterion-$variant-r$repetition"
    taskset -c 15 "$experiment_dir/bin/validation-$variant" --quick -L 0.1 \
      --resamples 1000 --csv "$output.csv" -o "$experiment_dir/logs/criterion-$variant-r$repetition.html" > "$output.log" 2>&1
  done
done
