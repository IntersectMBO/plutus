#!/usr/bin/env bash

# This script runs the given benchmark and compares the results against origin/master.
#
# USAGE: 
# In order to trigger benchmarking for an open PR, post a comment like `/benchmark NAME` to
# the PR. The command will be acknowledged with a :rocket: reaction and when done a bot will
# publish the results to the same PR.
# 
# This script can also be run locally inside the nix shell like so: 
# `BENCHMARK_NAME=nofib ./scripts/ci-plutus-benchmark.sh`
#
# NOTES:
# The `cabal update` command below is neccessary because while the whole script is executed inside
# a nix shell, this environment does not provide the hackage record inside .cabal and we have to 
# fetch/build this each time since we want to run this in a clean environment.
# The `jq` invocation below is necessary because we have to POST the PR comment as JSON data 
# (see the curl command) meaning the script output has to be escaped first before we can insert it.

set -e

if [ -z "$BENCHMARK_NAME" ] ; then
   echo "[ci-plutus-benchmark]: 'BENCHMARK_NAME' is not set, exiting."
   exit 1
fi
if [ -z "$PR_NUMBER" ] ; then
   echo "[ci-plutus-benchmark]: 'PR_NUMBER' is not set, probably running locally."
   PR_NUMBER="[local]"
fi

if [ -z "$PR_BRANCH" ] ; then
   echo "[ci-plutus-benchmark]: 'PR_BRANCH' is not set, probably running locally"
else 
   echo "[ci-plutus-benchmark]: 'PR_BRANCH' set to $PR_BRANCH, fetching origin ..."
   git fetch origin 
   git checkout "$PR_BRANCH"
fi

PR_BRANCH_REF=$(git rev-parse --short HEAD)

echo "[ci-plutus-benchmark]: Processing benchmark comparison for benchmark '$BENCHMARK_NAME' on PR $PR_NUMBER"

echo "[ci-plutus-benchmark]: Running as user:"
whoami 

echo "[ci-plutus-benchmark]: Updating cabal database ..."
cabal update

echo "[ci-plutus-benchmark]: Clearing caches with cabal clean ..."
cabal clean

echo "[ci-plutus-benchmark]: Running benchmark for PR branch at $PR_BRANCH_REF ..."
2>&1 cabal bench "$BENCHMARK_NAME" | tee bench-PR.log

echo "[ci-plutus-benchmark]: Switching branches ..."
git checkout "$(git merge-base HEAD origin/master)"
BASE_BRANCH_REF=$(git rev-parse --short HEAD)

echo "[ci-plutus-benchmark]: Clearing caches with cabal clean ..."
cabal clean

echo "[ci-plutus-benchmark]: Running benchmark for base branch at $BASE_BRANCH_REF ..."
2>&1 cabal bench "$BENCHMARK_NAME" | tee bench-base.log 
git checkout "$PR_BRANCH_REF"  # .. so we use the most recent version of the comparison script

echo "[ci-plutus-benchmark]: Comparing results ..."
{
# The blank line is important, otherwise Github doesn't render markdown in the body of the details element.
# See https://gist.github.com/ericclemmons/b146fe5da72ca1f706b2ef72a20ac39d for examples
cat <<EOF 
Comparing benchmark results of '$BENCHMARK_NAME' on '$BASE_BRANCH_REF' (base) and '$PR_BRANCH_REF' (PR)

<details>
<summary>Results table</summary>

EOF
./plutus-benchmark/bench-compare-markdown bench-base.log bench-PR.log "${BASE_BRANCH_REF:0:7}" "${PR_BRANCH_REF:0:7}"
echo -e "</details>"
} > bench-compare-result.log