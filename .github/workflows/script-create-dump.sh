#!/usr/bin/env bash

# Run a Cardano local node, and the script dump job
#
# Example usage:
#   AWS_ACCESS_KEY_ID=<...> \
#     AWS_SECRET_ACCESS_KEY=<...> \
#     AWS_DEFAULT_REGION=<...> \
#     AWS_ENDPOINT_URL=https://s3.devx.iog.io \
#     NODE_DIR=$HOME/mainnet \
#     S3_DUMP_DIR=s3://plutus/mainnet-script-dump/ \
#     DUMP_DIR=../mainnet-script-dump \
#     ./scripts/create-dump.sh

set -eEuo pipefail

trap '(kill $pid_node || true); (kill $pid_dump || true); exit' INT TERM QUIT ERR EXIT

mkdir -p "$NODE_DIR"
mkdir -p "$DUMP_DIR"

set -x

# Start running local node
./scripts/cardano-node.sh > /dev/null 2>&1 &

pid_node=$!

cabal update

# If the local node is run for the first time, the config file needs to be downloaded,
# so here we wait until the config file is available.
while ! [ -f "$NODE_DIR"/config.json ]
do
  sleep 15
done

# Start the dump job
cabal v2-run plutus-script-evaluation-test:dump-script-events -- --socket-path "$NODE_DIR"/db/node.socket --config "$NODE_DIR"/config.json --mainnet --blocks-per-file 50000 --events-per-file 50000 &
pid_dump=$!

echo $pid_node
echo $pid_dump
wait $pid_dump
wait $pid_node