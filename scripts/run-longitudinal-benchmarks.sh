#!/usr/bin/env bash

for bench in $BENCHMARKS; do 
  2>&1 cabal run "$bench" | tee "$bench-output.txt"
done 
python ./scripts/format-benchmark-output.py
