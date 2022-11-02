#!/usr/bin/env bash

# for some reason you can't just put a heredoc in a variable...
read -r -d '' USAGE << EOF
assemble-changelog.sh PACKAGE VERSION
  Assembles the changelog for PACKAGE at VERSION.
EOF

if [ "$#" == "0" ]; then
  echo "$USAGE"
fi

PACKAGE=$1
VERSION=$2

echo "Assembling changelog for $PACKAGE-$VERSION"
pushd $PACKAGE > /dev/null
scriv collect --version "$VERSION"
popd > /dev/null
