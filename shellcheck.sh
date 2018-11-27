#!/usr/bin/env bash

set -euo pipefail
exec "$(nix-build -E 'with import ./lib.nix; import iohkNix.tests.shellcheckScript {inherit pkgs;}')" "$@"
