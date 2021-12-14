#ifndef ED25519_H
#define ED25519_H

#include <stdlib.h>

#if defined(__cplusplus)
extern "C" {
#endif

typedef unsigned char ed25519_signature[64];
typedef unsigned char ed25519_public_key[32];
typedef unsigned char ed25519_unextended_secret_key[32]; // this is the UNEXTENDED SECRET KEY
typedef unsigned char ed25519_secret_key[64]; // this is the EXTENDED SECRET KEY

void cardano_crypto_ed25519_publickey(const ed25519_secret_key sk, ed25519_public_key pk);
int cardano_crypto_ed25519_sign_open(const unsigned char *m, size_t mlen, const ed25519_public_key pk, const ed25519_signature RS);
void cardano_crypto_ed25519_sign (const unsigned char *m, size_t mlen, const unsigned char *salt, size_t slen, const ed25519_secret_key sk, const ed25519_public_key pk, ed25519_signature RS);
int cardano_crypto_ed25519_scalar_add (const ed25519_secret_key sk1, const ed25519_secret_key sk2, ed25519_secret_key res);
int cardano_crypto_ed25519_point_add (const ed25519_public_key pk1, const ed25519_public_key pk2, ed25519_public_key res);
int cardano_crypto_ed25519_extend (const ed25519_unextended_secret_key seed, ed25519_secret_key secret);

#if defined(__cplusplus)
}
#endif

#endif // ED25519_H
