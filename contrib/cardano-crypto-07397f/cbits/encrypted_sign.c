#include <assert.h>
#include <stdint.h>
#include <string.h>

#include <ed25519.h>
#include <hmac.h>

#include "cryptonite_pbkdf2.h"

typedef uint8_t cryptonite_chacha_context[131];

extern void cryptonite_chacha_init(cryptonite_chacha_context *ctx, uint8_t nb_rounds, uint32_t keylen, const uint8_t *key, uint32_t ivlen, const uint8_t *iv);
extern void cryptonite_chacha_combine(uint8_t *dst, cryptonite_chacha_context *st, const uint8_t *src, uint32_t bytes);

void clear(void *buf, uint32_t const sz)
{
	/* FIXME - HERE we need to make sure the compiler is not going to remove the call */
	memset(buf, 0, sz);
}

#define NB_ITERATIONS 15000

static
void stretch(uint8_t *buf, uint32_t const buf_len, uint8_t const *pass, uint32_t const pass_len)
{
	const uint8_t salt[] = "encrypted wallet salt";
	assert(pass_len > 0);
	cryptonite_fastpbkdf2_hmac_sha512(pass, pass_len, salt, sizeof(salt), NB_ITERATIONS, buf, buf_len);
}

#define SYM_KEY_SIZE     32
#define SYM_NONCE_SIZE   8
#define SYM_BUF_SIZE     (SYM_KEY_SIZE+SYM_NONCE_SIZE)

#define SECRET_KEY_SEED_SIZE 32
#define ENCRYPTED_KEY_SIZE 64
#define PUBLIC_KEY_SIZE    32
#define CHAIN_CODE_SIZE    32

#define FULL_KEY_SIZE      (ENCRYPTED_KEY_SIZE + PUBLIC_KEY_SIZE + CHAIN_CODE_SIZE)

typedef struct {
	uint8_t ekey[ENCRYPTED_KEY_SIZE];
	uint8_t pkey[PUBLIC_KEY_SIZE];
	uint8_t cc[CHAIN_CODE_SIZE];
} encrypted_key;

typedef struct {
	uint8_t pkey[PUBLIC_KEY_SIZE];
	uint8_t cc[CHAIN_CODE_SIZE];
} public_key;

static void memory_combine(uint8_t const *pass, uint32_t const pass_len, uint8_t const *source, uint8_t *dest, uint32_t sz)
{
	uint8_t buf[SYM_BUF_SIZE];
	cryptonite_chacha_context ctx;
	static uint8_t const CHACHA_NB_ROUNDS = 20;

	if (pass_len) {
		memset(&ctx, 0, sizeof(cryptonite_chacha_context));

		/* generate BUF_SIZE bytes where first KEY_SIZE bytes is the key and NONCE_SIZE remaining bytes the nonce */
		stretch(buf, SYM_BUF_SIZE, pass, pass_len);
		cryptonite_chacha_init(&ctx, CHACHA_NB_ROUNDS, SYM_KEY_SIZE, buf, SYM_NONCE_SIZE, buf + SYM_KEY_SIZE);
		clear(buf, SYM_BUF_SIZE);
		cryptonite_chacha_combine(dest, &ctx, source, sz);
		clear(&ctx, sizeof(cryptonite_chacha_context));
	} else {
		memcpy(dest, source, sz);
	}
}

static void unencrypt_start
    (uint8_t const*  pass,
     uint32_t const  pass_len,
     encrypted_key const *encrypted_key /* in */,
     ed25519_secret_key  decrypted_key /* out */)
{
	memory_combine(pass, pass_len, encrypted_key->ekey, decrypted_key, ENCRYPTED_KEY_SIZE);
}

static void unencrypt_stop(ed25519_secret_key decrypted_key)
{
	clear(decrypted_key, sizeof(ed25519_secret_key));
}

static void wallet_encrypted_initialize
    (uint8_t const *pass, uint32_t const pass_len,
     const ed25519_secret_key secret_key,
     const uint8_t cc[CHAIN_CODE_SIZE],
     encrypted_key *encrypted_key)
{
	ed25519_public_key pub_key;

	cardano_crypto_ed25519_publickey(secret_key, pub_key);

	memory_combine(pass, pass_len, secret_key, encrypted_key->ekey, ENCRYPTED_KEY_SIZE);
	memcpy(encrypted_key->pkey, pub_key, PUBLIC_KEY_SIZE);
	memcpy(encrypted_key->cc, cc, CHAIN_CODE_SIZE);
}


int wallet_encrypted_from_secret
    (uint8_t const *pass, uint32_t const pass_len,
     const uint8_t seed[SECRET_KEY_SEED_SIZE],
     const uint8_t cc[CHAIN_CODE_SIZE],
     encrypted_key *encrypted_key)
{
	ed25519_secret_key secret_key;
	if (cardano_crypto_ed25519_extend(seed, secret_key))
		return 1;
	wallet_encrypted_initialize(pass, pass_len, secret_key, cc, encrypted_key);
	return 0;
}

int wallet_encrypted_new_from_mkg
    (uint8_t const *pass, uint32_t const pass_len,
     const uint8_t master_key[96],
     encrypted_key *encrypted_key)
{
	ed25519_secret_key secret_key;
	memcpy(secret_key, master_key, 64);
	secret_key[0] &= 248;   /* clears the bottom 3 bits */
	secret_key[31] &= 0x1F; /* clears the 3 highest bits */
	secret_key[31] |= 64;   /* set the 2nd highest bit */

	wallet_encrypted_initialize(pass, pass_len, secret_key, master_key + 64, encrypted_key);
	return 0;
}

void wallet_encrypted_sign
    (encrypted_key const *encrypted_key, uint8_t const* pass, uint32_t const pass_len,
     uint8_t const *data, uint32_t const data_len,
     ed25519_signature signature)
{
	ed25519_secret_key priv_key;
	ed25519_public_key pub_key;

	unencrypt_start(pass, pass_len, encrypted_key, priv_key);
	cardano_crypto_ed25519_publickey(priv_key, pub_key);
	cardano_crypto_ed25519_sign(data, data_len, encrypted_key->cc, CHAIN_CODE_SIZE, priv_key, pub_key, signature);
	unencrypt_stop(priv_key);
}

void wallet_encrypted_change_pass
    (encrypted_key const *in, uint8_t const *old_pass, uint32_t const old_pass_len,
    uint8_t const *new_pass, uint32_t const new_pass_len, encrypted_key *out)
{
	ed25519_secret_key priv_key;
	unencrypt_start(old_pass, old_pass_len, in, priv_key);
	memory_combine(new_pass, new_pass_len, priv_key, out->ekey, ENCRYPTED_KEY_SIZE);
	unencrypt_stop(priv_key);
	memcpy(out->pkey, in->pkey, PUBLIC_KEY_SIZE);
	memcpy(out->cc, in->cc, CHAIN_CODE_SIZE);
}

DECL_HMAC(sha512,
          SHA512_BLOCK_SIZE,
          SHA512_DIGEST_SIZE,
          struct sha512_ctx,
          cryptonite_sha512_init,
          cryptonite_sha512_update,
          cryptonite_sha512_finalize);

typedef enum {
	DERIVATION_V1 = 1,
	DERIVATION_V2 = 2,
} derivation_scheme_mode;

static void multiply8_v1(uint8_t *dst, uint8_t *src, int bytes)
{
	int i;
	uint8_t prev_acc = 0;
	for (i = 0; i < bytes; i++) {
		dst[i] = (src[i] << 3) + (prev_acc & 0x8);
		prev_acc = src[i] >> 5;
	}
}

static void multiply8_v2(uint8_t *dst, uint8_t *src, int bytes)
{
	int i;
	uint8_t prev_acc = 0;
	for (i = 0; i < bytes; i++) {
		dst[i] = (src[i] << 3) + (prev_acc & 0x7);
		prev_acc = src[i] >> 5;
	}
	dst[bytes] = src[bytes-1] >> 5;
}

static void add_256bits_v1(uint8_t *dst, uint8_t *src1, uint8_t *src2)
{
	int i;
	for (i = 0; i < 32; i++) {
		uint8_t a = src1[i];
		uint8_t b = src2[i];
		uint16_t r = a + b;
		dst[i] = r & 0xff;
	}
}

static void add_256bits_v2(uint8_t *dst, uint8_t *src1, uint8_t *src2)
{
	int i; uint8_t carry = 0;
	for (i = 0; i < 32; i++) {
		uint8_t a = src1[i];
		uint8_t b = src2[i];
		uint16_t r = (uint16_t) a + (uint16_t) b + (uint16_t) carry;
		dst[i] = r & 0xff;
		carry = (r >= 0x100) ? 1 : 0;
	}
}

#define TAG_DERIVE_Z_NORMAL    "\x2"
#define TAG_DERIVE_Z_HARDENED  "\x0"
#define TAG_DERIVE_CC_NORMAL   "\x3"
#define TAG_DERIVE_CC_HARDENED "\x1"

static int index_is_hardened(uint32_t index)
{
	return (index & (1 << 31));
}

/* sk1 is zl8 and contains only 29 bytes of active data,
 * so it's not going to overflow when adding to sk2 */
void scalar_add_no_overflow(const ed25519_secret_key sk1, const ed25519_secret_key sk2, ed25519_secret_key res)
{
    uint16_t r = 0; int i;
    for (i = 0; i < 32; i++) {
	    r = (uint16_t) sk1[i] + (uint16_t) sk2[i] + r;
	    res[i] = (uint8_t) r;
	    r >>= 8;
    }
}

static void serialize_index32(uint8_t *out, uint32_t index, derivation_scheme_mode mode)
{
	switch (mode) {
	case DERIVATION_V1: /* BIG ENDIAN */
		out[0] = index >> 24;
		out[1] = index >> 16;
		out[2] = index >> 8;
		out[3] = index;
		break;
	case DERIVATION_V2: /* LITTLE ENDIAN */
		out[3] = index >> 24;
		out[2] = index >> 16;
		out[1] = index >> 8;
		out[0] = index;
		break;
	}
}

static void add_left(ed25519_secret_key res_key, uint8_t *z, ed25519_secret_key priv_key, derivation_scheme_mode mode)
{
	uint8_t zl8[32];

	memset(zl8, 0, 32);
	switch (mode) {
	case DERIVATION_V1:
		/* get 8 * Zl */
		multiply8_v1(zl8, z, 32);

		/* Kl = 8*Zl + parent(K)l */
		cardano_crypto_ed25519_scalar_add(zl8, priv_key, res_key);
		break;
	case DERIVATION_V2:
		/* get 8 * Zl */
		multiply8_v2(zl8, z, 28);
		/* Kl = 8*Zl + parent(K)l */
		scalar_add_no_overflow(zl8, priv_key, res_key);
		break;
	}
}

static void add_right(ed25519_secret_key res_key, uint8_t *z, ed25519_secret_key priv_key, derivation_scheme_mode mode)
{
	switch (mode) {
	case DERIVATION_V1:
		add_256bits_v1(res_key + 32, z+32, priv_key+32);
		break;
	case DERIVATION_V2:
		add_256bits_v2(res_key + 32, z+32, priv_key+32);
		break;
	}
}

static void add_left_public(uint8_t *out, uint8_t *z, uint8_t *in, derivation_scheme_mode mode)
{
	uint8_t zl8[32];
	ed25519_public_key pub_zl8;

	memset(zl8, 0, 32);
	switch (mode) {
	case DERIVATION_V1:
		multiply8_v1(zl8, z, 32);
		break;
	case DERIVATION_V2:
		multiply8_v2(zl8, z, 28);
		break;
	}

	/* Kl = 8*Zl*B + Al */
	cardano_crypto_ed25519_publickey(zl8, pub_zl8);
	cardano_crypto_ed25519_point_add(pub_zl8, in, out);
}

void wallet_encrypted_derive_private
    (encrypted_key const *in,
     uint8_t const *pass, uint32_t const pass_len,
     uint32_t index,
     encrypted_key *out,
     derivation_scheme_mode mode)
{
	ed25519_secret_key priv_key;
	ed25519_secret_key res_key;
	HMAC_sha512_ctx hmac_ctx;
	uint8_t idxBuf[4];
	uint8_t z[64];
	uint8_t hmac_out[64];

	serialize_index32(idxBuf, index, mode);

	unencrypt_start(pass, pass_len, in, priv_key);

	/* calculate Z */
	HMAC_sha512_init(&hmac_ctx, in->cc, CHAIN_CODE_SIZE);
	if (index_is_hardened(index)) {
		HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_Z_HARDENED, 1);
		HMAC_sha512_update(&hmac_ctx, priv_key, ENCRYPTED_KEY_SIZE);
	} else {
		HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_Z_NORMAL, 1);
		HMAC_sha512_update(&hmac_ctx, in->pkey, PUBLIC_KEY_SIZE);
	}
	HMAC_sha512_update(&hmac_ctx, idxBuf, 4);
	HMAC_sha512_final(&hmac_ctx, z);

	add_left(res_key, z, priv_key, mode);

	/* Kr = Zr + parent(K)r */
	add_right(res_key, z, priv_key, mode);

	/* calculate the new chain code */
	HMAC_sha512_init(&hmac_ctx, in->cc, CHAIN_CODE_SIZE);
	if (index_is_hardened(index)) {
		HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_CC_HARDENED, 1);
		HMAC_sha512_update(&hmac_ctx, priv_key, ENCRYPTED_KEY_SIZE);
	} else {
		HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_CC_NORMAL, 1);
		HMAC_sha512_update(&hmac_ctx, in->pkey, PUBLIC_KEY_SIZE);
	}
	HMAC_sha512_update(&hmac_ctx, idxBuf, 4);
	HMAC_sha512_final(&hmac_ctx, hmac_out);

	unencrypt_stop(priv_key);

	wallet_encrypted_initialize(pass, pass_len, res_key, hmac_out + 32, out);
	clear(res_key, ENCRYPTED_KEY_SIZE);
	clear(hmac_out, 64);
}

int wallet_encrypted_derive_public
    (uint8_t *pub_in,
     uint8_t *cc_in,
     uint32_t index,
     uint8_t *pub_out,
     uint8_t *cc_out,
     derivation_scheme_mode mode)
{
	HMAC_sha512_ctx hmac_ctx;
	uint8_t idxBuf[4];
	uint8_t z[64];
	uint8_t hmac_out[64];

	/* cannot derive hardened key using public bits */
	if (index_is_hardened(index))
		return 1;

	serialize_index32(idxBuf, index, mode);

	/* calculate Z */
	HMAC_sha512_init(&hmac_ctx, cc_in, CHAIN_CODE_SIZE);
	HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_Z_NORMAL, 1);
	HMAC_sha512_update(&hmac_ctx, pub_in, PUBLIC_KEY_SIZE);
	HMAC_sha512_update(&hmac_ctx, idxBuf, 4);
	HMAC_sha512_final(&hmac_ctx, z);

	/* get 8 * Zl */
	add_left_public(pub_out, z, pub_in, mode);

	/* calculate the new chain code */
	HMAC_sha512_init(&hmac_ctx, cc_in, CHAIN_CODE_SIZE);
	HMAC_sha512_update(&hmac_ctx, TAG_DERIVE_CC_NORMAL, 1);
	HMAC_sha512_update(&hmac_ctx, pub_in, PUBLIC_KEY_SIZE);
	HMAC_sha512_update(&hmac_ctx, idxBuf, 4);
	HMAC_sha512_final(&hmac_ctx, hmac_out);

	memcpy(cc_out, hmac_out + (sizeof(hmac_out) - CHAIN_CODE_SIZE), CHAIN_CODE_SIZE);

	return 0;
}
