#include "cbits.h"
#include <string.h>

bool c_homogenous_naive(unsigned char const needle,
                        unsigned char const *restrict haystack,
                        size_t const len) {
  bool homogenous = true;
  for (size_t i = 0; i < len; i++) {
    if (haystack[i] != needle) {
      homogenous = false;
      break;
    }
  }
  return homogenous;
}

bool c_homogenous_sliding_window(unsigned char const needle,
                                 unsigned char const *restrict haystack,
                                 size_t len) {
  for (size_t i = 0; i < 16; i++) {
    if (len == 0) {
      return true;
    }
    if (haystack[0] != needle) {
      return false;
    }
    haystack++;
    len--;
  }
  return (memcmp(haystack - 16, haystack, len) == 0);
}
