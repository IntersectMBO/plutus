#!/usr/bin/env bash

# ci-plutus-benchmark: Run benchmarks on 2 branches, compare the results and
# add a comment on the corresponding PR on GitHub.
#
# This script is supposed to be executed by https://buildkite.com/input-output-hk/plutus-benchmark
# which itself is triggered through the GitHub workflow ./.github/workflows/benchmark.yaml
#
# USAGE: 
# In order to trigger benchmarking for an open PR, add `/benchmark` as a comment to
# the PR. The command will be acknowledged with a :rocket: reaction and when done a bot will
# add the results as comment to the same PR.
#
# NOTE:
# In order to post a comment to GitHub the buildkite runner needs to provide a
# GitHub token with permissions to add comments in '/run/keys/buildkite-github-token'
# otherwise this will fail.

set -e

if [ -z "$PR_NUMBER" ] ; then
   echo "[ci-plutus-benchmark]: 'PR_NUMBER' is not set! Exiting"
   exit 1
fi
echo "[ci-plutus-benchmark]: Processing benchmark comparison for PR $PR_NUMBER"

echo "[ci-plutus-benchmark]: Updating cabal database ..."
cabal update

echo "[ci-plutus-benchmark]: Running benchmark for PR branch ..."
cabal bench plutus-benchmark:validation >bench-PR.log 2>&1

echo "[ci-plutus-benchmark]: Switching branches ..."
git checkout "$(git merge-base HEAD master)"

echo "[ci-plutus-benchmark]: Running benchmark for base branch ..."
cabal bench plutus-benchmark:validation >bench-base.log 2>&1

echo "[ci-plutus-benchmark]: Comparing results ..."
./plutus-benchmark/bench-compare bench-base.log bench-PR.log >bench-compare-result.log
nix-shell -p jq --run "jq -Rs '.' bench-compare-result.log >bench-compare.json"

echo "[ci-plutus-benchmark]: Posting results to GitHub ..."
curl -s -H "Authorization: token $(</run/keys/buildkite-github-token)" -X POST -d "{\"body\": $(<bench-compare.json)}" "https://api.github.com/repos/input-output-hk/plutus/issues/${PR_NUMBER}/comments"
