#include "cbits.h"
#include <stdint.h>

size_t c_clz_naive(unsigned char const *src, size_t const len) {
  size_t leading_zeroes = 0;
  for (size_t i = 0; i < len; i++) {
    // Necessary because __builtin_clz has an undefined outcome if its argument
    // is zero.
    if (src[i] != 0) {
      // This is necessary because GCC will sign-extend the ith byte whether we
      // like it or not. Thus, we have to compensate.
      size_t offset = (sizeof(unsigned int) - 1) * 8;
      return leading_zeroes + (__builtin_clz(src[i]) - offset);
    }
    leading_zeroes += 8;
  }
  return leading_zeroes;
}

size_t c_clz_block(unsigned char const *restrict src, size_t len) {
  size_t leading_zeroes = 0;
  while (len >= sizeof(unsigned long long)) {
    unsigned long long x = *((unsigned long long const *restrict)src);
    if (x != 0) {
      return leading_zeroes + __builtin_clzll(x);
    }
    leading_zeroes += (sizeof(unsigned long long) * 8);
    src += sizeof(unsigned long long);
    len -= sizeof(unsigned long long);
  }
  while (len > 0) {
    if ((*src) != 0) {
      // Same necessity as before
      size_t offset = (sizeof(unsigned int) - 1) * 8;
      return leading_zeroes + (__builtin_clz(*src) - offset);
    }
    leading_zeroes += 8;
    src++;
    len--;
  }
  return leading_zeroes;
}

size_t c_clz_block_unrolled(unsigned char const *restrict src, size_t len) {
  size_t leading_zeroes = 0;
  while (len >= 2 * sizeof(unsigned long long)) {
    unsigned long long x = ((unsigned long long const *restrict)src)[0];
    unsigned long long y = ((unsigned long long const *restrict)src)[1];
    if (x != 0) {
      return leading_zeroes + __builtin_clzll(x);
    }
    if (y != 0) {
      return leading_zeroes + sizeof(unsigned long long) + __builtin_clzll(y);
    }
    leading_zeroes += (sizeof(unsigned long long) * 16);
    src += 2 * sizeof(unsigned long long);
    len -= 2 * sizeof(unsigned long long);
  }
  while (len > 0) {
    if ((*src) != 0) {
      // Same necessity as before
      size_t offset = (sizeof(unsigned int) - 1) * 8;
      return leading_zeroes + (__builtin_clz(*src) - offset);
    }
    leading_zeroes += 8;
    src++;
    len--;
  }
  return leading_zeroes;
}
