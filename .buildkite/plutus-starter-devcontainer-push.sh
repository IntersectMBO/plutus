#!/usr/bin/env bash

nix-build default.nix -A build-and-push-devcontainer-script -o build-and-push-image.sh
./build-and-push-image.sh
