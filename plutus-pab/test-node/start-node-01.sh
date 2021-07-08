#!/bin/bash

cabal exec cardano-node -- run \
    --config configuration.yaml \
    --topology node1/topology.json \
    --database-path node1/db \
    --socket-path node1/node.sock \
    --shelley-kes-key node1/kes.skey \
    --shelley-vrf-key genesis/delegate-keys/delegate1.vrf.skey \
    --shelley-operational-certificate node1/cert \
    --port 3001
