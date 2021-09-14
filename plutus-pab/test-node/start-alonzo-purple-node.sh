#!/bin/bash

cabal exec cardano-node -- run \
    --config alonzo-purple/alonzo-purple-config.json \
    --topology alonzo-purple/alonzo-purple-topology.json \
    --database-path alonzo-purple/db \
    --socket-path alonzo-purple/node-server.sock \
    --port 3003
