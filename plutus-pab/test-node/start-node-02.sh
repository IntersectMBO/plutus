#!/bin/bash

cardano-node run \
    --config configuration.yaml \
    --topology node2/topology.json \
    --database-path node2/db \
    --socket-path node2/node.sock \
    --shelley-kes-key node2/kes.skey \
    --shelley-vrf-key genesis/delegate-keys/delegate-key2.vrf.skey \
    --shelley-operational-certificate node2/cert \
    --port 3002
