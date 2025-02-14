#!/usr/bin/env bash

set -euo pipefail

cabal clean 
cabal update
cabal build all --enable-profiling --enable-library-profiling

