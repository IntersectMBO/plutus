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
  "cabal run haskell-conformance -- --accept"
  "cabal run haskell-steppable-conformance -- --accept"
  "cabal run agda-conformance -- --accept"
)
tests_plutus_tx_plugin=(
  "cabal run plutus-tx-plugin-tests -- --accept"
  "cabal run size -- --accept"
)
tests_plutus_ledger_api=(
  "cabal run plutus-ledger-api-test -- --accept"
  "cabal run plutus-ledger-api-plugin-test -- --accept"
)
tests_plutus_benchmark=(
  "cabal run plutus-benchmark-nofib-tests -- --accept"
  "cabal run plutus-benchmark-lists-tests -- --accept"
  "cabal run ed25519-costs-test -- --accept"
  "cabal run bls12-381-costs-test -- --accept"
  "cabal run plutus-benchmark-script-contexts-tests -- --accept"
  "cabal run plutus-benchmark-marlowe-tests -- --accept"
  "cabal run bitwise-test -- --accept"
  "cabal run coop-test -- --accept"
  "cabal run linear-vesting-test -- --accept"
  "cabal run cardano-loans-test -- --accept"
)
tests_cardano_constitution=(
  "cabal run cardano-constitution-test -- --accept"
)
tests_plutus_tx=(
  "cabal run plutus-tx-test -- --accept"
)
tests_plutus_core=(
  "cabal run plutus-core-test -- --accept"
  "cabal run untyped-plutus-core-test -- --accept"
  "cabal run plutus-ir-test -- --accept"
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
