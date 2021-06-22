#!/bin/sh

if [ -z "$BUILDKITE_API_ACCESS_TOKEN" ] ; then
    echo "[trigger-buildkite]: 'BUILDKITE_API_ACCESS_TOKEN' is not set!"
    exit 1
fi

if [ -z "$GITHUB_REF" ] ; then
    echo "[trigger-buildkite]: 'GITHUB_REF' is not set!"
    exit 1
fi

curl -H "Authorization: Bearer $BUILDKITE_API_ACCESS_TOKEN" "https://api.buildkite.com/v2/organizations/input-output-hk/pipelines/plutus-benchmark/builds" \
  -X "POST" \
  -F "commit=HEAD" \
  -F "branch=${GITHUB_REF##*/}" \
  -F "message=benchmark"
