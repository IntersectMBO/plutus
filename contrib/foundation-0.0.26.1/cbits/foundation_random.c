
#include <stdlib.h>
#include <assert.h>
#include <stddef.h>
#include <errno.h>
#include <string.h>
#include "foundation_prim.h"
#include "foundation_system.h"
#include "foundation_bits.h"

#if defined(FOUNDATION_SYSTEM_LINUX)
#include <sys/syscall.h>
#include <sys/types.h>
#include <unistd.h>
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#endif

#include <stdio.h>

#if defined(FOUNDATION_SYSTEM_LINUX) && defined(SYS_getrandom)
int foundation_sysrandom_linux(void *buf, size_t length)
{
	unsigned int flags = 1; /* RANDOM=0x2, NONBLOCK=0x1 */
	size_t i = 0;

	/* special case to detect availability */
	if (length == 0) {
		int r = syscall(SYS_getrandom, buf, 0, flags);
		return (r == -1) ? -1 : 0;
	}

	while (i < length) {
		int r = syscall(SYS_getrandom, buf + i, length - i, flags);
		if (r <= 0) {
			if (errno != -EAGAIN)
				return -errno;
		}
		if (r > 0)
			i += r;
	}
	return 0;
}
#else
int foundation_sysrandom_linux(void *buf, size_t length) { return -ENODEV; }
#endif

#define CHACHA_KEY_SIZE 32
#define CHACHA_NONCE_SIZE 16
#define CHACHA_OUTPUT_SIZE 64

#define CHACHA_KEY_SIZE32 8
#define CHACHA_NONCE_SIZE32 4
#define CHACHA_OUTPUT_SIZE32 16

#define QR(a,b,c,d) \
	a += b; d = rol32(d ^ a,16); \
	c += d; b = rol32(b ^ c,12); \
	a += b; d = rol32(d ^ a, 8); \
	c += d; b = rol32(b ^ c, 7);

static void chacha_core(int rounds,
		        uint8_t out8[CHACHA_OUTPUT_SIZE],
                        const uint8_t key8[CHACHA_KEY_SIZE],
                        const uint8_t nonce8[CHACHA_NONCE_SIZE])
{
	uint32_t x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15;
	int i;
	static const uint8_t sigma8[16] = "expand 32-byte k";
	uint32_t *out = (uint32_t *) out8;
	uint32_t *key = (uint32_t *) key8;
	uint32_t *nonce = (uint32_t *) nonce8;
	uint32_t *sigma = (uint32_t *) sigma8;

	x0  = sigma[0]; x1  = sigma[1]; x2  = sigma[2]; x3  = sigma[3];
	x4  = key[0]  ; x5  = key[1]  ; x6  = key[2]  ; x7  = key[3]  ;
	x8  = key[4]  ; x9  = key[5]  ; x10 = key[6]  ; x11 = key[7]  ;
	x12 = nonce[0]; x13 = nonce[1]; x14 = nonce[2]; x15 = nonce[3];

	for (i = rounds; i > 0; i -= 2) {
		QR(x0, x4, x8, x12);
		QR(x1, x5, x9, x13);
		QR(x2, x6, x10, x14);
		QR(x3, x7, x11, x15);

		QR(x0, x5, x10, x15);
		QR(x1, x6, x11, x12);
		QR(x2, x7, x8, x13);
		QR(x3, x4, x9, x14);
	}

	x0  += sigma[0]; x1  += sigma[1]; x2  += sigma[2]; x3  += sigma[3];
	x4  += key[0]  ; x5  += key[1]  ; x6  += key[2]  ; x7  += key[3]  ;
	x8  += key[4]  ; x9  += key[5]  ; x10 += key[6]  ; x11 += key[7]  ;
	x12 += nonce[0]; x13 += nonce[1]; x14 += nonce[2]; x15 += nonce[3];

	out[0] = cpu_to_le32(x0);
	out[1] = cpu_to_le32(x1);
	out[2] = cpu_to_le32(x2);
	out[3] = cpu_to_le32(x3);
	out[4] = cpu_to_le32(x4);
	out[5] = cpu_to_le32(x5);
	out[6] = cpu_to_le32(x6);
	out[7] = cpu_to_le32(x7);
	out[8] = cpu_to_le32(x8);
	out[9] = cpu_to_le32(x9);
	out[10] = cpu_to_le32(x10);
	out[11] = cpu_to_le32(x11);
	out[12] = cpu_to_le32(x12);
	out[13] = cpu_to_le32(x13);
	out[14] = cpu_to_le32(x14);
	out[15] = cpu_to_le32(x15);
}

int foundation_rngV1_generate(uint8_t newkey[CHACHA_KEY_SIZE], uint8_t *dst, uint8_t key[CHACHA_KEY_SIZE], FsCountOf bytes)
{
	const int rounds = 20;
	uint8_t nonce[CHACHA_NONCE_SIZE] = { 0 };
	uint8_t buf[CHACHA_OUTPUT_SIZE]; /* for partial buffer */

	if (!bytes)
		return 0;
	for (; bytes >= CHACHA_OUTPUT_SIZE; bytes -= CHACHA_OUTPUT_SIZE, dst += CHACHA_OUTPUT_SIZE) {
		chacha_core(rounds, dst, key, nonce);
		if (++nonce[0] == 0)
			nonce[1]++;
	}

	assert(bytes < CHACHA_OUTPUT_SIZE);

	chacha_core(rounds, buf, key, nonce);
	int remaining = CHACHA_OUTPUT_SIZE - bytes;
	if (remaining >= CHACHA_KEY_SIZE) {
		memcpy(dst, buf, bytes);
		memcpy(newkey, buf + bytes, CHACHA_KEY_SIZE);
	} else {
		memcpy(dst, buf, bytes);
		if (++nonce[0] == 0)
			nonce[1]++;
		chacha_core(rounds, buf, key, nonce);
		memcpy(newkey, buf, CHACHA_KEY_SIZE);
	}
	memset(buf, 0, CHACHA_OUTPUT_SIZE);
	return 0;
}

int foundation_rngV1_generate_word32(uint8_t newkey[CHACHA_KEY_SIZE], uint32_t *dst_w, uint8_t key[CHACHA_KEY_SIZE])
{
	return foundation_rngV1_generate(newkey, (uint8_t*)dst_w, key, sizeof(uint32_t));
}

int foundation_rngV1_generate_word64(uint8_t newkey[CHACHA_KEY_SIZE], uint64_t *dst_w, uint8_t key[CHACHA_KEY_SIZE])
{
	return foundation_rngV1_generate(newkey, (uint8_t*)dst_w, key, sizeof(uint64_t));
}

int foundation_rngV1_generate_f32(uint8_t newkey[CHACHA_KEY_SIZE], float *dst_w, uint8_t key[CHACHA_KEY_SIZE])
{
	uint32_t const UPPER_MASK = 0x3F800000UL;
	uint32_t const LOWER_MASK = 0x007FFFFFUL;
	uint32_t tmp32;
	int r = foundation_rngV1_generate_word32(newkey, &tmp32, key);
	tmp32 = UPPER_MASK | (tmp32 & LOWER_MASK);
	*dst_w = (float)tmp32 - 1.0;
	return r;
}

int foundation_rngV1_generate_f64(uint8_t newkey[CHACHA_KEY_SIZE], double *dst_w, uint8_t key[CHACHA_KEY_SIZE])
{
	uint64_t const UPPER_MASK = 0x3FF0000000000000ULL;
	uint64_t const LOWER_MASK = 0x000FFFFFFFFFFFFFULL;
	uint64_t tmp64;
	int r = foundation_rngV1_generate_word64(newkey, &tmp64, key);
	tmp64 = UPPER_MASK | (tmp64 & LOWER_MASK);
	*dst_w = (double)tmp64 - 1.0;
	return r;
}
