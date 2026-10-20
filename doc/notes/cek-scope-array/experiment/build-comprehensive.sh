#!/usr/bin/env bash
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
root_dir="$(cd -- "$experiment_dir/../../../.." && pwd)"
variant="$1"
cd "$root_dir"
python3 "$experiment_dir/select-variant.py" "$variant"
targets=(validation validation-full marlowe nofib force-delay)
components=()
for target in "${targets[@]}"; do components+=("plutus-benchmark:bench:$target"); done
cabal build -j4 "${components[@]}"
mkdir -p "$experiment_dir/bin/comprehensive" "$experiment_dir/build/comprehensive-$variant"
for target in "${targets[@]}"; do
  cp -- "$(cabal list-bin "plutus-benchmark:bench:$target")" "$experiment_dir/bin/comprehensive/$target-$variant"
done
cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N1 \
  -outputdir "$experiment_dir/build/comprehensive-$variant" \
  -o "$experiment_dir/bin/comprehensive/server-$variant" "$experiment_dir/Comprehensive.hs" \
  -package plutus-core -package plutus-ledger-api -package deepseq -package bytestring \
  -package-id plutus-benchmark-0.1.0.0-inplace-plutus-benchmark-common \
  -package-id plutus-benchmark-0.1.0.0-inplace-validation-internal \
  -package-id plutus-benchmark-0.1.0.0-inplace-marlowe-internal \
  -package-id plutus-benchmark-0.1.0.0-inplace-nofib-internal
export plutus_benchmark_datadir="$root_dir/plutus-benchmark"
"$experiment_dir/bin/comprehensive/server-$variant" catalog "$root_dir/plutus-benchmark" \
  > "$experiment_dir/logs/comprehensive-catalog-$variant.tsv"
for target in "${targets[@]}"; do
  "$experiment_dir/bin/comprehensive/$target-$variant" --list \
    > "$experiment_dir/logs/comprehensive-$target-$variant.list"
done
sha256sum "$experiment_dir/bin/comprehensive/"*"-$variant"
