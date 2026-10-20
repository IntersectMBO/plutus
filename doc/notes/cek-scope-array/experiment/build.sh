#!/usr/bin/env bash
# Run from a Plutus GHC 9.6 development shell. Keeps separate immutable binaries.
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
variant="${1:-baseline}"
bench_source="${SCOPE_BENCH_SOURCE:-$experiment_dir/Bench.hs}"
cd -- "$root_dir"
mkdir -p "$experiment_dir/bin" "$experiment_dir/build/$variant" "$experiment_dir/logs"
python3 "$experiment_dir/select-variant.py" "$variant"
canonical="${SCOPE_BUILD_CANONICAL:-0}"
if [[ "$variant" == baseline || "$variant" == compact-checked || "$canonical" == 1 ]]; then
  canonical=1
  cabal build -j4 plutus-benchmark:bench:validation
else
  cabal build -j4 plutus-core:lib:plutus-core
fi
cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N1 \
  -outputdir "$experiment_dir/build/$variant" \
  -o "$experiment_dir/bin/$variant" "$bench_source" \
  -package plutus-core -package-id plutus-core-1.71.0.0-inplace-flat -package criterion \
  -package bytestring -package vector -package deepseq -package data-default-class
sha256sum "$experiment_dir/bin/$variant"
if [[ "$canonical" == 1 ]]; then
  cp -- "$(cabal list-bin plutus-benchmark:bench:validation)" "$experiment_dir/bin/validation-$variant"
  sha256sum "$experiment_dir/bin/validation-$variant"
fi

if [[ "$variant" != baseline && "$variant" != ra-erased* ]]; then
  array_options=()
  if [[ "$variant" == fixed* ]]; then array_options+=(-DFIXED_ARRAY); fi
  cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N2 \
    "${array_options[@]}" -outputdir "$experiment_dir/build/$variant/env-checks" \
    -o "$experiment_dir/bin/env-checks-$variant" "$experiment_dir/EnvChecks.hs" \
    -package plutus-core -package deepseq
  "$experiment_dir/bin/env-checks-$variant"
fi
"$experiment_dir/bin/$variant" check "$root_dir/plutus-benchmark/validation/data" \
  > "$experiment_dir/logs/check-$variant.tsv"
cmp <(gzip -cd "$experiment_dir/../results/check-baseline.tsv.gz") "$experiment_dir/logs/check-$variant.tsv"
echo "PASS: $variant agrees with baseline results, budgets, and logs"
