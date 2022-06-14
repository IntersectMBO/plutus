#!/usr/bin/env bash

# Sync an S3 prefix to a local directory, and unzip the bz2 files
# Example usage:
#   LOCAL_DIR=/tmp/script-dump/ \
#     AWS_ACCESS_KEY_ID=<...> \
#     AWS_SECRET_ACCESS_KEY=<...> \
#     AWS_DEFAULT_REGION=<...> \
#     AWS_ENDPOINT_URL=https://s3.devx.iog.io \
#     ./s3-sync-unzip.sh \
#     s3://plutus/script-evaluation-dump/ \
#     \*.event.bz2

set -euo pipefail

S3_PREFIX=$1
S3_SUFFIX=${2:-"*"}

mkdir -p "$LOCAL_DIR"

set -x
aws --endpoint-url "$AWS_ENDPOINT_URL" s3 sync "$S3_PREFIX" "$LOCAL_DIR" --exclude "*" --include "$S3_SUFFIX"
bunzip2 -k "$LOCAL_DIR"/*.bz2 || ({ set +x; } 2>/dev/null; true)
