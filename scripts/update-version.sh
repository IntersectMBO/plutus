#!/usr/bin/env bash

# for some reason you can't just put a heredoc in a variable...
read -r -d '' USAGE << EOF
update-version.sh PACKAGE VERSION
  Updates the version for PACKAGE to VERSION, and updates bounds
  on that package in other cabal files.
EOF

if [ "$#" == "0" ]; then
  echo "$USAGE"
fi

set -euo pipefail

PACKAGE=$1
VERSION=$2

versioned_packages_regex=$(printf "\|%s" "${versioned_packages[@]}")
versioned_packages_regex="\(${versioned_packages_regex:2}\)"

IFS='.' read -r -a components <<< "$VERSION"

major_version="${components[0]}.${components[1]}"

echo "Updating version of $PACKAGE to $VERSION"
# update package version in cabal file for package
sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal"

# update version bounds in all cabal files
# It looks for patterns like the following:
#
# - ", plutus-core"
# - ", plutus-core:uplc"
# - ", plutus-core ^>=1.0"
# - ", plutus-core:{plutus-core, plutus-core-testlib}  ^>=1.0"
#
# and updates the version bounds to "^>={major version}"
echo "Updating version bounds on $PACKAGE to '>=$major_version'"
find . -name "*.cabal" -exec sed -i "s/\(, $PACKAGE[^^]*\).*/\1 ^>=$major_version/" {} \;
