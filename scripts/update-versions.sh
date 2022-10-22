#!/usr/bin/env bash

set -euo pipefail

versioned_packages=(
  "plutus-core"
  "plutus-ledger-api"
  "plutus-tx"
  "plutus-tx-plugin"
)

additional_packages=( "$@" )
versioned_packages+=( "${additional_packages[@]:1}" )

versioned_packages_regex=$(printf "\|%s" "${versioned_packages[@]}")
versioned_packages_regex="\(${versioned_packages_regex:2}\)"

IFS='.' read -r -a components <<< "$1"

major_version="${components[0]}.${components[1]}"

# update package versions in cabal files for versioned packages
find . -regex ".*/$versioned_packages_regex\.cabal" -exec sed -i "s/\(^version:\s*\).*/\1$1/" {} \;

# update version bounds in all cabal files
# It looks for patterns like the following:
#
# - ", plutus-core"
# - ", plutus-core:uplc"
# - ", plutus-core ^>=1.0"
# - ", plutus-core:{plutus-core, plutus-core-testlib}  ^>=1.0"
#
# and updates the version bounds to "^>={major version}"
find . -name "*.cabal" -exec sed -i "s/\(, ${versioned_packages_regex}[^^]*\).*/\1 ^>=$major_version/" {} \;
