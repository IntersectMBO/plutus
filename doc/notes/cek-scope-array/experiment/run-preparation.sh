#!/usr/bin/env bash
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
cd -- "$root_dir"
# The baseline library must already be built (selecting source alone is not enough).
[[ "$(cat "$experiment_dir/.selected")" == baseline ]]
mkdir -p "$experiment_dir/build/preparation"
cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N1 -main-is Prep.main \
  -outputdir "$experiment_dir/build/preparation" -o "$experiment_dir/bin/preparation" \
  "$experiment_dir/Prep.hs" "$experiment_dir/Bench.hs" \
  -package plutus-core -package-id plutus-core-1.71.0.0-inplace-flat \
  -package criterion -package bytestring -package vector -package deepseq \
  -package data-default-class
for repetition in 1 2 3 4 5; do
  taskset -c 15 "$experiment_dir/bin/preparation" "$root_dir/plutus-benchmark/validation/data" 0.01 \
    +RTS -N1 -T -RTS > "$experiment_dir/../results/preparation-r$repetition.csv"
done
