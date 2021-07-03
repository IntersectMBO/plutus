#!/bin/env bash

set -ex

killall plutus-pab || true

rm -rf pab-core.db* 

cabal run exe:plutus-pab -- migrate pab-core.db

# Ensure marlowe apps are up-to-date
cd ../marlowe && cabal build && cd -

contracts=(marlowe-app marlowe-companion-app marlowe-follow-app)

for c in "${contracts[@]}"; do
  # shellcheck disable=SC2086
  cabal run exe:plutus-pab -- \
    --config plutus-pab.yaml  \
    contracts install --path "$(cabal exec -- which $c)"
done;

cabal run exe:plutus-pab -- \
  --config plutus-pab.yaml  \
  contracts installed

cabal run exe:plutus-pab -- --ekg --config plutus-pab.yaml all-servers
