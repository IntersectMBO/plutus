#!/usr/bin/env bash

set -e

if [ $# -ne 3 ]; then
    echo "[trigger-buildkite-pipeline]: Missing argument(s)"
    echo "[trigger-buildkite-pipeline]: expecting 3 arguments: <branch name> <PR number> <benchmark name>"
    echo "[trigger-buildkite-pipeline]: Arguments received: '$*'"
    exit 1
fi

if [ -z "$BUILDKITE_API_ACCESS_TOKEN" ] ; then
   echo "[trigger-buildkite-pipeline]: 'BUILDKITE_API_ACCESS_TOKEN' is not set!"
   exit 1
fi

BRANCH="$1"
PR_NUMBER="$2"
BENCHMARK_NAME="$3"

echo "[trigger-buildkite-pipeline]: Triggering build of benchmark $BENCHMARK_NAME for branch $BRANCH on PR $PR_NUMBER"

curl --silent -H "Authorization: Bearer $BUILDKITE_API_ACCESS_TOKEN" \
     -X POST "https://api.buildkite.com/v2/organizations/input-output-hk/pipelines/plutus-benchmark/builds"\
     -d "{
         \"commit\": \"HEAD\",
         \"branch\": \"$BRANCH\",
         \"message\": \"Running benchmarks\",
           \"env\": {
             \"PR_NUMBER\": \"$PR_NUMBER\",
             \"BENCHMARK_NAME\": \"$BENCHMARK_NAME\"
           }
         }"