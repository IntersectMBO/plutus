#include "cbits.h"
#include <string.h>

bool c_bit_at(size_t const ix, unsigned char *const restrict src) {
  size_t big_ix = ix / 8;
  size_t small_ix = ix % 8;
  return src[big_ix] & (0x80 >> small_ix);
}

void c_bit_set_naive(bool const b, size_t const ix, unsigned char *restrict dst,
                     unsigned char const *restrict src, size_t const len) {
  size_t big_ix = ix / 8;
  size_t small_ix = ix % 8;
  for (size_t i = 0; i < len; i++) {
    dst[i] = src[i];
  }
  if (b == true) {
    dst[big_ix] = src[big_ix] | (0x80 >> small_ix);
  } else {
    dst[big_ix] = src[big_ix] & (~(0x80 >> small_ix));
  }
}

void c_bit_set_memcpy(bool const b, size_t const ix,
                      unsigned char *restrict dst,
                      unsigned char const *restrict src, size_t const len) {
  size_t big_ix = ix / 8;
  size_t small_ix = ix % 8;
  // Copy entirety of src
  memcpy(dst, src, len);
  // Set our desired bit
  if (b == true) {
    dst[big_ix] = src[big_ix] | (0x80 >> small_ix);
  } else {
    dst[big_ix] = src[big_ix] & (~(0x80 >> small_ix));
  }
}
