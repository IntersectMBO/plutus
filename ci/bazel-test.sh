#!/usr/bin/env nix-shell
#!nix-shell -p bazel python -i bash -I nixpkgs=https://github.com/NixOS/nixpkgs/archive/09195057114a0a8d112c847a9a8f52957420857d.tar.gz

set -euo pipefail

echo '~~~ Running tests with Bazel'

command time --format '%e' -o eval-time.txt \
    bazel test --remote_http_cache=https://bazel-cache:"$BAZEL_PASS"@bazel-cache.aws.iohkdev.io/plutus  //...

EVAL_TIME=$(cat eval-time.txt)
rm eval-time.txt

echo -e "\\e[32;1mOK: evaluation completed in $EVAL_TIME seconds with no errors\\e[0m"
