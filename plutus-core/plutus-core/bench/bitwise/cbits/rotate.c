#include "cbits.h"

void c_rotate_bits(int bit_rotation, unsigned char *restrict dst,
                   unsigned char const *restrict src, size_t len) {
  if (bit_rotation > 0) {
    size_t read_pos = bit_rotation / 8;
    size_t bit_tail_len = bit_rotation % 8;
    size_t write_pos = 0;
    unsigned char const tail_mask = (0x01 << bit_tail_len) - 1;
    unsigned char const head_mask = ~tail_mask;
    while (write_pos < len) {
      if (read_pos == len - 1) {
        dst[write_pos] = (head_mask & src[read_pos]) | (tail_mask & src[0]);
        read_pos = 0;
      } else {
        dst[write_pos] =
            (head_mask & src[read_pos]) | (tail_mask & src[read_pos + 1]);
        read_pos++;
      }
      write_pos++;
    }
  } else {
    c_rotate_bits((len * 8) + bit_rotation, dst, src, len);
  }
}
