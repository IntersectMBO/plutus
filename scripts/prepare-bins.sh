#!/usr/bin/env bash

set -euo pipefail

echo -e "Preparing static binaries for release..."

for exec in "uplc pir plc"; do 
  echo "Building $exec..."
  nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.$exec"
  echo "Compressing $exec..."
  upx -9 ./result/bin/$exec -o "$exec-x86_64-linux-ghc96" --force-overwrite
done 