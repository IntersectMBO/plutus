#!/usr/bin/env bash
set -euo pipefail


# Usage: ./scripts/regen-goldens.sh [all|ghc96|ghc912|current]
#
# Golden files are GHC-version-specific (tests write into 9.6/ or 9.12/
# subdirectories depending on the compiler they were built with), so the
# tests must be run once per GHC version. By default ('all') this script
# re-runs itself inside both the ghc96 and ghc912 nix dev shells.
# 'current' skips nix and runs with whatever toolchain is already on PATH.

shells=()
case "${1:-all}" in
  all)     shells=(ghc96 ghc912) ;;
  ghc96)   shells=(ghc96) ;;
  ghc912)  shells=(ghc912) ;;
  current) ;;
  *) echo "usage: $0 [all|ghc96|ghc912|current]" >&2; exit 1 ;;
esac

if [ "${#shells[@]}" -gt 0 ]; then
  script="$(readlink -f "$0")"
  status=0
  for shell in "${shells[@]}"; do
    echo "=== Regenerating goldens in the $shell dev shell"
    nix develop --no-warn-dirty --accept-flake-config ".#$shell" \
      --command "$script" current || status=1
  done
  exit "$status"
fi

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


# tests_<project> run under every GHC version; tests_<project>_ghc96 only run
# when the current compiler is GHC 9.6, because those components are marked
# 'buildable: False' for other versions ('ghc-version-support' in the cabal
# files), so `cabal run` for them fails outright under e.g. GHC 9.12.
#
# NB: agda-conformance deliberately runs without --accept: some of its tests
# are expected failures, and accepting would overwrite the goldens that
# haskell-conformance just regenerated with Agda error messages (see the note
# in plutus-conformance.cabal). It's a consistency check, not a regen step.
tests_plutus_conformance=(
  "cabal run haskell-conformance -- --accept"
  "cabal run haskell-conformance -- --format=flat --accept"
  "cabal run haskell-steppable-conformance -- --accept"
  "cabal run haskell-steppable-conformance -- --format=flat --accept"
)
tests_plutus_conformance_ghc96=(
  "cabal run agda-conformance"
  "cabal run agda-conformance -- --format=flat"
)
tests_plutus_tx_plugin=(
  "cabal run plutus-tx-plugin-tests -- --accept"
  "cabal run size -- --accept"
  "cabal run plutus-ledger-api-plugin-test -- --accept"
)
tests_plutus_tx_plugin_ghc96=()
tests_plutus_ledger_api=(
  "cabal run plutus-ledger-api-test -- --accept"
)
tests_plutus_ledger_api_ghc96=()
tests_plutus_benchmark=()
tests_plutus_benchmark_ghc96=(
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
tests_cardano_constitution=()
tests_cardano_constitution_ghc96=(
  "cabal run cardano-constitution-test -- --accept"
)
tests_plutus_tx=(
  "cabal run plutus-tx-test -- --accept"
)
tests_plutus_tx_ghc96=()
tests_plutus_core=(
  "cabal run plutus-core-test -- --accept"
  "cabal run untyped-plutus-core-test -- --accept"
  "cabal run plutus-ir-test -- --accept"
)
tests_plutus_core_ghc96=()

ghc_minor="$(ghc --numeric-version | cut -d. -f1-2)"

# Run all tests, continuing past failures and reporting them at the end
failures=()
for project in "${projects[@]}"; do
  echo "=== Entering $project"
  cd "$project"

  # Construct the names of the tests arrays (replace - with _)
  varname="tests_${project//-/_}[@]"
  varname_ghc96="tests_${project//-/_}_ghc96[@]"
  cmds=("${!varname}")
  if [ "$ghc_minor" = "9.6" ]; then
    cmds+=("${!varname_ghc96}")
  else
    for skipped in "${!varname_ghc96}"; do
      echo "-> Skipping (GHC 9.6 only): $skipped"
    done
  fi

  for cmd in "${cmds[@]}"; do
    echo "-> $cmd"
    if ! $cmd; then
      echo "FAILURE in '$project': command failed -> $cmd" >&2
      failures+=("$project: $cmd")
    fi
    clear || true
  done

  cd ..
done

if [ "${#failures[@]}" -gt 0 ]; then
  echo "The following commands failed:" >&2
  printf ' - %s\n' "${failures[@]}" >&2
  exit 1
fi

echo "All tests passed!"
