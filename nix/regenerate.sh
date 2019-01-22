#!/usr/bin/env bash

set -euo pipefail

exec $(nix-build `dirname $0`/iohk-common.nix -A nix-tools.regeneratePackages --no-out-link)
