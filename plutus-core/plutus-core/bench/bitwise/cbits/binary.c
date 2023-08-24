#include "cbits.h"

void c_and_naive(unsigned char *dst, unsigned char const *src1,
                 unsigned char const *src2, size_t const len) {
  for (size_t i = 0; i < len; i++) {
    dst[i] = src1[i] & src2[i];
  }
}
