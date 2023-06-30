#include "cbits.h"
#include <stdlib.h>
#include <string.h>

void c_shift_bits(int bit_shift, unsigned char *restrict dst,
                  unsigned char const *restrict src, size_t len) {
  if (bit_shift > 0) {
    size_t infill_bytes = bit_shift / 8;
    size_t const bit_head_len = bit_shift % 8;
    if (infill_bytes > len) {
      infill_bytes = len;
    }
    memset(dst, 0x00, infill_bytes);
    if (bit_head_len == 0) {
      memcpy(dst + infill_bytes, src, len - infill_bytes);
    } else {
      size_t read_pos = 0;
      size_t write_pos = infill_bytes;
      unsigned char const hi_mask = (0x01 << bit_head_len) - 1;
      unsigned char const lo_mask = ~hi_mask;
      while (write_pos < len) {
        if (read_pos == 0) {
          dst[write_pos] = hi_mask & src[read_pos];
        } else {
          dst[write_pos] =
              (lo_mask & src[read_pos - 1]) | (hi_mask & src[read_pos]);
        }
        write_pos++;
        read_pos++;
      }
    }
  } else {
    size_t const abs_bit_shift = abs(bit_shift);
    size_t infill_bytes = abs_bit_shift / 8;
    size_t const bit_tail_len = abs_bit_shift % 8;
    if (infill_bytes > len) {
      infill_bytes = len;
    }
    if (bit_tail_len == 0) {
      memcpy(dst, src + infill_bytes, len - infill_bytes);
    } else {
      size_t read_pos = infill_bytes;
      size_t write_pos = 0;
      unsigned char const hi_mask = (0x01 << bit_tail_len) - 1;
      unsigned char const lo_mask = ~hi_mask;
      while (read_pos < len) {
        if (read_pos == (len - 1)) {
          dst[write_pos] = lo_mask & src[read_pos];
        } else {
          dst[write_pos] =
              (lo_mask & src[read_pos]) | (hi_mask & src[read_pos + 1]);
        }
        write_pos++;
        read_pos++;
      }
    }
    memset(dst + (len - infill_bytes), 0x00, infill_bytes);
  }
}
