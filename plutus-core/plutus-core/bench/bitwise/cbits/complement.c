#include "cbits.h"
#include <stdint.h>

void c_complement_naive(unsigned char *restrict dst,
                        unsigned char const *restrict src, size_t const len) {
  for (size_t i = 0; i < len; i++) {
    dst[i] = ~(src[i]);
  }
}
