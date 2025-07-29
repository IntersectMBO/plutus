#!/usr/bin/env bash
set -euo pipefail

# List of sub‑projects and their tests
projects=(
  "plutus-conformance"
  "plutus-tx-plugin"
  "plutus-ledger-api"
  "plutus-benchmark"
  "cardano-constitution"
  "plutus-tx"
  "plutus-core"
)

tests_plutus_conformance=(
  "cabal run haskell-conformance -- --accept --hide-successes"
  "cabal run haskell-steppable-conformance -- --accept --hide-successes"
  "cabal run agda-conformance -- --accept --hide-successes"
)
tests_plutus_tx_plugin=(
  "cabal run plutus-tx-plugin-tests -- --accept --hide-successes"
  "cabal run size -- --accept --hide-successes"
)
tests_plutus_ledger_api=(
  "cabal run plutus-ledger-api-test -- --accept --hide-successes"
  "cabal run plutus-ledger-api-plugin-test -- --accept --hide-successes"
)
tests_plutus_benchmark=(
  'cabal test plutus-benchmark --test-options="--accept" --test-options="--hide-successes"'
)
tests_cardano_constitution=(
  "cabal run cardano-constitution-test -- --accept --hide-successes"
)
tests_plutus_tx=(
  "cabal run plutus-tx-test -- --accept --hide-successes"
)
tests_plutus_core=(
  "cabal run plutus-core-test -- --accept --hide-successes"
  "cabal run untyped-plutus-core-test -- --accept --hide-successes"
  "cabal run plutus-ir-test -- --accept --hide-successes"
)

# Run all tests
for project in "${projects[@]}"; do
  echo "=== Entering $project"
  cd "$project"

  # Construct the name of the tests array (replace - with _)
  varname="tests_${project//-/_}[@]"
  for cmd in "${!varname}"; do
    echo "-> $cmd"
    if ! $cmd; then
      echo "FAILURE in '$project': command failed -> $cmd" >&2
      exit 1
    fi
    clear
  done

  cd ..
done

echo "All tests passed!"
