#!/usr/bin/env bash

# Run a Cardano local node, and the script dump job
#
# Example usage:
# AWS_ACCESS_KEY_ID=<...> \
#   AWS_SECRET_ACCESS_KEY=<...> \
#   AWS_DEFAULT_REGION=<...> \
#   AWS_ENDPOINT_URL=https://s3.devx.iog.io \
#   NODE_DIR=../cardano-node-files \
#   NODE_BIN_DIR=../cardano-node-bin \
#   S3_DUMP_DIR=s3://plutus/mainnet-script-dump/ \
#   LOCAL_DUMP_DIR=../mainnet-script-dump \
#   ./scripts/create-dump.sh

set -eEuo pipefail

trap '(kill $pid_node || true); (kill $pid_dump || true); exit' INT TERM QUIT ERR EXIT

set -x

mkdir -p "$NODE_DIR"
mkdir -p "$NODE_BIN_DIR"
mkdir -p "$LOCAL_DUMP_DIR"

# Start running local node
./scripts/cardano-node.sh > /dev/null 2>&1 &

pid_node=$!

# If the local node is run for the first time, the config file needs to be downloaded,
# so here we wait until the config file is available.
while ! [ -f "$NODE_DIR"/mainnet-config.json ]
do
  sleep 30
done

cabal update
# Start the dump job
cabal v2-run plutus-script-evaluation-test:dump-script-events -- --socket-path "$NODE_DIR"/db/node.socket --config "$NODE_DIR"/mainnet-config.json --mainnet --blocks-per-file 10000 --events-per-file 50000 --dir "$LOCAL_DUMP_DIR" &
pid_dump=$!

echo $pid_node
echo $pid_dump
wait $pid_dump
wait $pid_node
