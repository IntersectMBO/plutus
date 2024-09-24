#!/usr/bin/env bash

set -euo pipefail

banner='\n
Lets prepare binaries for a release:\n
 1. Build `pir`\n
 2. Compress `pir` with `upx`\n
 3. Build `uplc`\n
 4. Compress `uplc` with `upx`\n
'

echo -e $banner

echo "Building pir..."

nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.pir"

echo "Compressing pir..."

upx -9 ./result/bin/pir -o pir-x86_64-linux-ghc96 --force-overwrite

echo "Building uplc..."

nix build ".#hydraJobs.x86_64-linux.musl64.ghc96.uplc"

echo "Compressing uplc..."

upx -9 ./result/bin/uplc -o uplc-x86_64-linux-ghc96 --force-overwrite
