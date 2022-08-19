#include "cbits.h"

bool c_bit_at(size_t const ix, unsigned char *const restrict src,
              size_t const len) {
  size_t big_len = ix / 8;
  size_t small_len = ix % 8;
  return src[big_len] & (0x80 >> small_len);
}
