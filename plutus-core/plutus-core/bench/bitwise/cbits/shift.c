#include "cbits.h"
#include <string.h>

void c_shift_bytes(int shift, unsigned char *restrict dst,
                   unsigned char const *restrict src, size_t const len) {
  if (shift < 0) {
    int const abs_shift = abs(shift);
    memcpy(dst, src + abs_shift, len - abs_shift);
    memset(dst + abs_shift, 0x00, abs_shift);
  } else {
    memset(dst, 0x00, shift);
    memcpy(dst + shift, src, len - shift);
  }
}
