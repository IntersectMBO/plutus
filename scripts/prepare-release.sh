#!/usr/bin/env bash

# for some reason you can't just put a heredoc in a variable...
read -r -d '' USAGE << EOF
prepare-release.sh VERSION [PACKAGE...]
  Prepares to release PACKAGEs at VERSION. If no PACKAGEs are provided,
  prepares to release the default packges.
EOF

if [ "$#" == "0" ]; then
  echo "$USAGE"
fi

set -euo pipefail

VERSION=$1

shift

default_packages=(
  "plutus-core"
  "plutus-ledger-api"
  "plutus-tx"
  "plutus-tx-plugin"
)

release_packages=( "$@" )

if [ ${#release_packages[@]} -eq 0 ]; then
  release_packages+=( "${default_packages[@]}" )
fi

echo "Preparing release for ${release_packages[*]}"
echo ""
echo "Updating versions ..."
for package in "${release_packages[@]}"; do
  $(dirname $0)/update-version.sh "$package" "$VERSION"
done

echo ""
echo "Assembling changelogs ..."
for package in "${release_packages[@]}"; do
  $(dirname $0)/assemble-changelog.sh "$package" "$VERSION"
done
