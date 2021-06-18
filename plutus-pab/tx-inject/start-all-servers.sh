#!/bin/bash
rm -f ./primary.db
cabal build plutus-pab
cabal exec plutus-pab -- --config=./config.yaml migrate primary.db
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-currency"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-atomic-swap"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-game"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/plutus-pay-to-wallet"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-credential-manager"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-mirror"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-unlock-sto"
cabal exec plutus-pab -- --config=./config.yaml contracts install --path "$(stack path --local-install-root)/bin/prism-unlock-exchange"
cabal exec plutus-pab -- --config=./config.yaml all-servers "$1"
