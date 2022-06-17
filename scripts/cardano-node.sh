#!/usr/bin/env bash

# Run a mainnet Cardano node.
# Example usage:
#
# NODE_BIN_DIR=../cardano-node-bin \
#   NODE_DIR=../cardano-node
#   ./scripts/cardano-node.sh

set -euo pipefail

node_zipped="cardano-node-1.34.1-linux.tar.gz"
node_config_files=(
  "mainnet-config.json"
  "mainnet-byron-genesis.json"
  "mainnet-shelley-genesis.json"
  "mainnet-alonzo-genesis.json"
  "mainnet-topology.json"
)

trap 'kill $cardano_node_pid; exit' INT TERM QUIT

set -x
mkdir -p "$NODE_BIN_DIR"
# Download cardano-node binary
wget -nc https://hydra.iohk.io/build/13065769/download/1/$node_zipped -P "$NODE_BIN_DIR"

tar zxvf "$NODE_BIN_DIR"/$node_zipped -C "$NODE_BIN_DIR"

mkdir -p "$NODE_DIR"
# Download config files
for x in "${node_config_files[@]}"; do
  wget -nc https://hydra.iohk.io/build/7370192/download/1/"$x" -P "$NODE_DIR"
done

# Launch node
"$NODE_BIN_DIR"/cardano-node run \
  --config "$NODE_DIR"/mainnet-config.json \
  --topology "$NODE_DIR"/mainnet-topology.json \
  --database-path "$NODE_DIR"/db/ \
  --socket-path "$NODE_DIR"/db/node.socket \
  --host-addr 127.0.0.1 \
  --port 1337 &

cardano_node_pid=$!
wait $cardano_node_pid
