#!/usr/bin/env bash

# build cryptonite and cardano-crypto C sources with emscripten

# first run symlink the cbits subdirs of the cryptonite and cardano-crypto packages:
#  ln -s ../cryptonite/cbits cryptonite
#  ln -s ../cardano-crypto/cbits cardano-crypto


emcc -o crypto-cbits.js -s WASM=0 \
  -s "EXPORTED_FUNCTIONS=['_cryptonite_sha256_init', '_cryptonite_sha256_update', '_cryptonite_sha256_finalize'\
                         ,'_cryptonite_sha512_init', '_cryptonite_sha512_update', '_cryptonite_sha512_finalize'\
                         ,'_cryptonite_sha3_init', '_cryptonite_sha3_update', '_cryptonite_sha3_finalize'\
                         ,'_cryptonite_blake2b_init', '_cryptonite_blake2b_update', '_cryptonite_blake2b_finalize'\
                         ,'_cryptonite_fastpbkdf2_hmac_sha512'\
                         ,'_cardano_crypto_ed25519_sign_open', '_cardano_crypto_ed25519_sign', '_cardano_crypto_ed25519_publickey'\
                         ,'_cardano_crypto_ed25519_point_add'\
                         ,'_wallet_encrypted_derive_public', '_wallet_encrypted_derive_private', '_wallet_encrypted_derive_public'\
                         ,'_wallet_encrypted_sign', '_wallet_encrypted_from_secret', '_wallet_encrypted_change_pass'\
                         ,'_wallet_encrypted_new_from_mkg']" \
  -I. -Icryptonite/decaf/include -Icryptonite/decaf/include/arch_32 -Icryptonite/blake2/ref -Idecaf/p448 -Idecaf/p448/arch_32 -Icardano-crypto -Icardano-crypto/ed25519 \
  ./cardano-crypto/encrypted_sign.c \
  ./cardano-crypto/ed25519/ed25519.c \
  ./cryptonite/cryptonite_sha256.c \
  ./cryptonite/cryptonite_sha512.c \
  ./cryptonite/cryptonite_sha3.c \
  ./cryptonite/cryptonite_pbkdf2.c \
  ./cryptonite/cryptonite_blake2b.c \
  ./cryptonite/blake2/ref/blake2b-ref.c \
  ./cryptonite/cryptonite_chacha.c

google-closure-compiler --js=crypto-cbits.js --js_output_file=crypto-cbits.min.js
