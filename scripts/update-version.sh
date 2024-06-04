#!/usr/bin/env bash

usage () {
  echo "usage: $(basename $0) PACKAGE VERSION
  Updates the version for PACKAGE to VERSION, and updates bounds
  on that package in other cabal files."
}

if [[ $# != 2 ]]; then
  echo "Wrong number of arguments"
  usage
  exit 1
fi

set -euo pipefail

PACKAGE=$1
VERSION=$2

IFS='.' read -r -a components <<< "$VERSION"

major_version="${components[0]}.${components[1]}"

echo "Updating version of $PACKAGE to $VERSION"
# update package version in cabal file for package
sed -i "s/\(^version:\s*\).*/\1$VERSION/" "./$PACKAGE/$PACKAGE.cabal"

# Update version bounds in all cabal files
# It looks for patterns like the following:
#
# - ", plutus-core"
# - ", plutus-core:uplc"
# - ", plutus-core ^>=1.0"
# - ", plutus-core:{plutus-core, plutus-core-testlib}  ^>=1.0"
#
# and updates the version bounds to "^>={major version}"
#
# The ?* pattern prevents 'find' from attempting to modify ".cabal" (no basename).
#
# The pattern $PACKAGE[^-A-Za-z0-1][^^] matches exactly the package name followed by anything
# up to ^. We need [^-A-Za-z0-1] to prevent eg `plutus-tx` from matching `plutus-tx-plugin`.
#
# The second sed command is to match the case where the package name is at the end of the line:
# we need this because the first case requires at least one character after the package name.
#
# Note that this all requires a comma (maybe preceded and/or followed by whitespace) at the
# start of the line: it won't work with commas at the end.

echo "Updating version bounds on $PACKAGE to '^>=$major_version'"
find . -name "?*.cabal" -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE[^-A-Za-z0-1][^^]*\).*/\1^>=$major_version/" {} \; \
                        -exec sed -i "s/\(^[ \t]*,[ \t]*$PACKAGE$\)/\1 ^>=$major_version/" {} \;
