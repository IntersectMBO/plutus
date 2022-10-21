#!/usr/bin/env bash

set -euo pipefail

versioned_packages="\(plutus-core\|plutus-ledger-api\|plutus-tx\|plutus-tx-plugin\)"

IFS='.' read -r -a components <<< "$1"

major_version="${components[0]}.${components[1]}"

# update package versions in cabal files for versioned packages
find . -regex ".*/$versioned_packages\.cabal" -exec sed -i "s/\(^version:\s*\).*/\1$1/" {} \;

# update version bounds in all cabal files
find . -name "*.cabal" -exec sed -i "s/\(, ${versioned_packages}[^^]*\).*/\1 ^>=$major_version/" {} \;
