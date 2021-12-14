#!/usr/bin/env bash

set -euo pipefail

# build cryptonite and cardano-crypto C sources with emscripten

# first run symlink the cbits subdirs of the cryptonite and cardano-crypto packages:
#  ln -s ../cryptonite/cbits cryptonite
#  ln -s ../cardano-crypto/cbits cardano-crypto


emcc -o crypto-cbits.js -s WASM=0 \
  -s ERROR_ON_UNDEFINED_SYMBOLS=0 \
  -s "EXPORTED_RUNTIME_METHODS=['printErr']" \
  -s "EXPORTED_FUNCTIONS=['_malloc', '_free'\
                         ,'_cardano_crypto_ed25519_sign_open', '_cardano_crypto_ed25519_sign', '_cardano_crypto_ed25519_publickey'\
                         ,'_cardano_crypto_ed25519_point_add'\
                         ,'_wallet_encrypted_derive_public', '_wallet_encrypted_derive_private', '_wallet_encrypted_derive_public'\
                         ,'_wallet_encrypted_sign', '_wallet_encrypted_from_secret', '_wallet_encrypted_change_pass'\
                         ,'_wallet_encrypted_new_from_mkg']" \
  -I. -I../../cbits \
  -I../../cbits/ \
  -I../../cbits/ed25519 \
  ../../cbits/encrypted_sign.c \
  ../../cbits/ed25519/ed25519.c \
  --js-library extern.js

closure-compiler --js=crypto-cbits.js --js_output_file=crypto-cbits.min.js

cat crc32.js crypto-cbits.pre.js crypto-cbits.js crypto-cbits.post.js crypto-wrappers.js > ../cardano-crypto.js
