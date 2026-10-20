#!/usr/bin/env bash
set -euo pipefail
experiment_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
variant="$(cat "$experiment_dir/.selected")"
cabal exec -- ghc -O2 -threaded -rtsopts -with-rtsopts=-N2 \
  -outputdir "$experiment_dir/build/$variant/closure-checks" \
  -o "$experiment_dir/bin/closure-checks-$variant" -main-is ClosureChecks \
  "$experiment_dir/ClosureChecks.hs" "$experiment_dir/Bench.hs" \
  -package plutus-core -package-id plutus-core-1.71.0.0-inplace-flat \
  -package criterion -package bytestring -package vector -package deepseq \
  -package data-default-class
"$experiment_dir/bin/closure-checks-$variant" > "$experiment_dir/logs/closure-checks-$variant.tsv"
"$experiment_dir/bin/closure-checks-$variant" concurrent
if [[ "$variant" == *reuse* || "$variant" == *escape* ]]; then
  cabal exec -- ghc -O2 -outputdir "$experiment_dir/build/$variant/reuse-checks" \
    -o "$experiment_dir/bin/reuse-checks-$variant" "$experiment_dir/ReuseChecks.hs" \
    -package plutus-core
  "$experiment_dir/bin/reuse-checks-$variant"
fi
