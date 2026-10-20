#!/usr/bin/env bash
# Selects a separately instrumented candidate, never used for timing.
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
variant="$1-stats"
python3 "$experiment_dir/select-variant.py" "$variant"
cabal build -j4 plutus-core:lib:plutus-core
cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N1 \
  -outputdir "$experiment_dir/build/$variant" \
  -o "$experiment_dir/bin/$variant" -main-is ClosureStats \
  "$experiment_dir/ClosureStats.hs" "$experiment_dir/Bench.hs" \
  -package plutus-core -package-id plutus-core-1.71.0.0-inplace-flat \
  -package criterion -package bytestring -package vector -package deepseq \
  -package data-default-class
"$experiment_dir/bin/$variant" "$root_dir/plutus-benchmark/validation/data" \
  > "$experiment_dir/../results/$variant.csv"
