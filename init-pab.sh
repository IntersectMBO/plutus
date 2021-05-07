#!/bin/bash

echo Marlowe PAB Init

CONFIG=/home/jann/plutus/plutus-pab/plutus-pab.yaml
COMPANION=/home/jann/plutus/dist-newstyle/build/x86_64-linux/ghc-8.10.4.20210212/marlowe-0.1.0.0/x/marlowe-companion-app/build/marlowe-companion-app/marlowe-companion-app
MARLOWE=/home/jann/plutus/dist-newstyle/build/x86_64-linux/ghc-8.10.4.20210212/marlowe-0.1.0.0/x/marlowe-app/build/marlowe-app/marlowe-app

killall plutus-pab

rm -rf pab-core.db*
cabal build exe:plutus-pab
cabal exec plutus-pab -- migrate pab-core.db
cabal exec plutus-pab -- --config $CONFIG contracts install -p $COMPANION
cabal exec plutus-pab -- --config $CONFIG contracts install -p $MARLOWE
cabal exec plutus-pab -- --config $CONFIG contracts installed

echo Starting PAB
export GHCRTS='-T'
cabal exec plutus-pab -- -em --config $CONFIG all-servers