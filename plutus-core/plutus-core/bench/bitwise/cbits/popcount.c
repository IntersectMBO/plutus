#include "cbits.h"
#include <stdint.h>

size_t c_popcount_naive(unsigned char const *restrict src, size_t const len) {
  size_t total = 0;
  for (size_t i = 0; i < len; i++) {
    total += __builtin_popcount(src[i]);
  }
  return total;
}

/*
 * We take advantage of the fact that a single POPCNT instruction can count an
 * entire register's worth of bits, rather than a single byte. To aid GCC in
 * doing this, we do a classic strip mine: first count at unsigned long long
 * width, then finish off with byte-at-a-time.
 *
 * Strip mining:
 * http://physics.ujep.cz/~zmoravec/prga/main_for/mergedProjects/optaps_for/common/optaps_vec_mine.htm
 */
size_t c_popcount_block(unsigned char const *restrict src, size_t len) {
  size_t total = 0;
  while (len >= sizeof(unsigned long long)) {
    total += __builtin_popcountll(*(unsigned long long const *restrict)src);
    src += sizeof(unsigned long long);
    len -= sizeof(unsigned long long);
  }
  while (len > 0) {
    total += __builtin_popcount(*src);
    src++;
    len--;
  }
  return total;
}

/*
 * We further extend the popcount_block method by manually two-way unrolling
 * the loop. This can take advantage of high throughput for the POPCNT
 * instruction on modern x86 CPUs, as they can issue four POPCNT instructions
 * simultaneously if data is available.
 *
 * Loop unrolling:
 * https://en.wikipedia.org/wiki/Loop_unrolling#Static/manual_loop_unrolling
 * Instruction tables for x86:
 * https://www.agner.org/optimize/instruction_tables.pdf ILP (including
 * multiple-issue): https://en.wikipedia.org/wiki/Instruction-level_parallelism
 * Data dependency: https://en.wikipedia.org/wiki/Data_dependency
 */
size_t c_popcount_block_unroll(unsigned char const *restrict src, size_t len) {
  size_t total = 0;
  while (len >= 2 * sizeof(unsigned long long)) {
    total += __builtin_popcountll(*(unsigned long long const *restrict)src);
    total += __builtin_popcountll(*(
        unsigned long long const *restrict)(src + sizeof(unsigned long long)));
    src += 2 * sizeof(unsigned long long);
    len -= 2 * sizeof(unsigned long long);
  }
  while (len > 0) {
    total += __builtin_popcount(*src);
    src++;
    len--;
  }
  return total;
}
