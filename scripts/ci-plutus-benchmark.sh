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
# NOTES:
# (1) In order to post a comment to GitHub the buildkite runner needs to provide a
#     GitHub token with permissions to add comments in '/run/keys/buildkite-github-token'
#     otherwise this will fail.
# (2) The `cabal update` command below is neccessary because while the whole script
#     is executed inside a nix-shell, this environment does not provide the hackage
#     record inside .cabal and we have to fetch/build this each time since we want
#     to run this in a clean environment.
# (3) The `jq` invocation below is necessary because we have to POST the PR comment
#     as JSON data (see the curl command) meaning the script output has to be escaped
#     first before we can insert it.

set -e

if [ -z "$PR_NUMBER" ] ; then
   echo "[ci-plutus-benchmark]: 'PR_NUMBER' is not set! Exiting"
   exit 1
fi
echo "[ci-plutus-benchmark]: Processing benchmark comparison for PR $PR_NUMBER"
PR_BRANCH_REF=$(git show-ref -s HEAD)

echo "[ci-plutus-benchmark]: Updating cabal database ..."
cabal update

echo "[ci-plutus-benchmark]: Running benchmark for PR branch ..."
nix-shell --run "cabal bench plutus-benchmark:validation >bench-PR.log 2>&1"

echo "[ci-plutus-benchmark]: Switching branches ..."
git checkout "$(git merge-base HEAD master)"
BASE_BRANCH_REF=$(git show-ref -s HEAD)

echo "[ci-plutus-benchmark]: Running benchmark for base branch ..."
nix-shell --run "cabal bench plutus-benchmark:validation >bench-base.log 2>&1"

git checkout "$PR_BRANCH_REF"  # .. so we use the most recent version of the comparison script

echo "[ci-plutus-benchmark]: Comparing results ..."
echo -e "Comparing benchmark results of '$BASE_BRANCH_REF' (base) and '$PR_BRANCH_REF' (PR)\n" >bench-compare-result.log
./plutus-benchmark/bench-compare-markdown bench-base.log bench-PR.log "${BASE_BRANCH_REF:0:7}" "${PR_BRANCH_REF:0:7}" >>bench-compare-result.log
nix-shell -p jq --run "jq -Rs '.' bench-compare-result.log >bench-compare.json"

echo "[ci-plutus-benchmark]: Posting results to GitHub ..."
curl -s -H "Authorization: token $(</run/keys/buildkite-github-token)" -X POST -d "{\"body\": $(<bench-compare.json)}" "https://api.github.com/repos/input-output-hk/plutus/issues/${PR_NUMBER}/comments"
