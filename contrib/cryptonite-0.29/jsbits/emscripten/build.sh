#!/usr/bin/env bash

set -euo pipefail

# build cryptonite and cardano-crypto C sources with emscripten

# first run symlink the cbits subdirs of the cryptonite and cardano-crypto packages:
#  ln -s ../cryptonite/cbits cryptonite
#  ln -s ../cardano-crypto/cbits cardano-crypto


emcc -o crypto-cbits.js -s WASM=0 \
  -s "EXPORTED_RUNTIME_METHODS=['printErr']" \
  -s "EXPORTED_FUNCTIONS=['_malloc', '_free'\
                         ,'_cryptonite_md5_init', '_cryptonite_md5_update', '_cryptonite_md5_finalize'\
                         ,'_cryptonite_sha256_init', '_cryptonite_sha256_update', '_cryptonite_sha256_finalize'\
                         ,'_cryptonite_sha512_init', '_cryptonite_sha512_update', '_cryptonite_sha512_finalize'\
                         ,'_cryptonite_sha3_init', '_cryptonite_sha3_update', '_cryptonite_sha3_finalize'\
                         ,'_cryptonite_blake2b_init', '_cryptonite_blake2b_update', '_cryptonite_blake2b_finalize'\
                         ,'_cryptonite_poly1305_init', '_cryptonite_poly1305_update', '_cryptonite_poly1305_finalize'\
                         ,'_cryptonite_chacha_init', '_cryptonite_chacha_combine', '_cryptonite_chacha_generate'\
                         ,'_cryptonite_chacha_random'\
                         ,'_cryptonite_chacha_init_core'\
                         ,'_cryptonite_fastpbkdf2_hmac_sha512'\
                         ,'_cryptonite_ed25519_point_base_scalarmul'\
                         ,'_cryptonite_ed25519_point_encode'\
                         ,'_cryptonite_ed25519_scalar_decode_long'\
                         ,'_cryptonite_ed25519_sign_open'\
                         ,'_cryptonite_ed25519_sign'\
                         ,'_cryptonite_ed25519_publickey'\
                         ,'_cryptonite_ed25519_point_add' ]" \
  -I. -I../../cbits \
  -I../../cbits/decaf/include \
  -I../../cbits/decaf/include/arch_32 \
  -I../../cbits/blake2/ref \
  -I../../cbits/decaf/p448 \
  -I../../cbits/decaf/p448/arch_32 \
  ../../cbits/ed25519/ed25519.c \
  ../../cbits/cryptonite_md5.c \
  ../../cbits/cryptonite_sha256.c \
  ../../cbits/cryptonite_sha512.c \
  ../../cbits/cryptonite_sha3.c \
  ../../cbits/cryptonite_pbkdf2.c \
  ../../cbits/cryptonite_blake2b.c \
  ../../cbits/blake2/ref/blake2b-ref.c \
  ../../cbits/cryptonite_chacha.c \
  ../../cbits/cryptonite_poly1305.c

closure-compiler --js=crypto-cbits.js --js_output_file=crypto-cbits.min.js

cat crc32.js crypto-cbits.pre.js crypto-cbits.js crypto-cbits.post.js crypto-wrappers.js > ../cryptonite.js

  # -Icardano-crypto \
  # -Icardano-crypto/ed25519 \
  # ./cardano-crypto/encrypted_sign.c \
  # ./cardano-crypto/ed25519/ed25519.c \
                        #  ,'_cardano_crypto_ed25519_sign_open', '_cardano_crypto_ed25519_sign', '_cardano_crypto_ed25519_publickey'\
                        #  ,'_cardano_crypto_ed25519_point_add'\
                        #  ,'_wallet_encrypted_derive_public', '_wallet_encrypted_derive_private', '_wallet_encrypted_derive_public'\
                        #  ,'_wallet_encrypted_sign', '_wallet_encrypted_from_secret', '_wallet_encrypted_change_pass'\
                        #  ,'_wallet_encrypted_new_from_mkg']" \
