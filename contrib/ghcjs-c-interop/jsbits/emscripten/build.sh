#!/usr/bin/env bash

set -euo pipefail

# build cryptonite and cardano-crypto C sources with emscripten

# first run symlink the cbits subdirs of the cryptonite and cardano-crypto packages:
#  ln -s ../cryptonite/cbits cryptonite
#  ln -s ../cardano-crypto/cbits cardano-crypto

PKG=test

emcc -o $PKG-cbits.js -s WASM=0 \
  -s ERROR_ON_UNDEFINED_SYMBOLS=0 \
  -s ALLOW_TABLE_GROWTH \
  -s "EXPORTED_RUNTIME_METHODS=['printErr','addFunction','removeFunction']" \
  -s "EXPORTED_FUNCTIONS=['_malloc', '_free',\
                          '_test_fold']" \
  -I. -I../../cbits \
  ../../cbits/test.c \
  --js-library extern.js

#closure-compiler --js=crypto-cbits.js --js_output_file=crypto-cbits.min.js

cat $PKG-cbits.pre.js $PKG-cbits.js $PKG-cbits.post.js $PKG-wrappers.js > ../$PKG.js
