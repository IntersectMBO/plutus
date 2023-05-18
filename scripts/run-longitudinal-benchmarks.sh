#!/usr/bin/env bash

set -euo pipefail

# We shouldn't need this if we're running in a nix shell, but
# we currently do because of https://github.com/input-output-hk/haskell.nix/issues/1955
cabal update
for bench in $BENCHMARKS; do 
  2>&1 cabal run "$bench" | tee "$bench-output.txt"
done 
python ./scripts/format-benchmark-output.py
