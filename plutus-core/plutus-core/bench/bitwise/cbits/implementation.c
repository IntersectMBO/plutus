#include "cbits.h"

void c_and_implementation_3(unsigned char *dst, unsigned char const *src1,
                            unsigned char const *src2, size_t const len) {
  if (len != 0) {
    size_t const big_step_size = sizeof(unsigned long long);
    size_t const biggest_step_size = big_step_size * 4; // four-way unroll
    size_t const biggest_steps = len / biggest_step_size;
    size_t const rest = len % biggest_step_size;
    size_t const big_steps = rest / big_step_size;
    size_t const small_steps = rest % big_step_size;
    unsigned long long *big_ptr1 = (unsigned long long *)src1;
    unsigned long long *big_ptr2 = (unsigned long long *)src2;
    unsigned long long *big_dst = (unsigned long long *)dst;
    for (size_t i = 0; i < biggest_steps; i++) {
      // We have to do this as GCC is unreliable at unrolling, even if the loop
      // has fixed length, we have enough registers _and_ we turn on O2.
      unsigned long long const x1 = *big_ptr1;
      unsigned long long const x2 = *(big_ptr1 + 1);
      unsigned long long const x3 = *(big_ptr1 + 2);
      unsigned long long const x4 = *(big_ptr1 + 3);
      unsigned long long const y1 = *big_ptr2;
      unsigned long long const y2 = *(big_ptr2 + 1);
      unsigned long long const y3 = *(big_ptr2 + 2);
      unsigned long long const y4 = *(big_ptr2 + 3);
      *big_dst = x1 & y1;
      *(big_dst + 1) = x2 & y2;
      *(big_dst + 2) = x3 & y3;
      *(big_dst + 3) = x4 & y4;
      big_ptr1 += 4;
      big_ptr2 += 4;
      big_dst += 4;
    }
    for (size_t i = 0; i < big_steps; i++) {
      unsigned long long const x = *big_ptr1;
      unsigned long long const y = *big_ptr2;
      *big_dst = x & y;
      big_ptr1++;
      big_ptr2++;
      big_dst++;
    }
    unsigned char *small_ptr1 = (unsigned char *)big_ptr1;
    unsigned char *small_ptr2 = (unsigned char *)big_ptr2;
    unsigned char *small_dst = (unsigned char *)big_dst;
    for (size_t i = 0; i < small_steps; i++) {
      unsigned char const x = *small_ptr1;
      unsigned char const y = *small_ptr2;
      *small_dst = x & y;
      small_ptr1++;
      small_ptr2++;
      small_dst++;
    }
  }
}

void c_and_implementation(unsigned char *dst, unsigned char const *src1,
                          unsigned char const *src2, size_t const len) {
  if (len != 0) {
    size_t const big_step_size = sizeof(unsigned long long);
    size_t const big_steps = len / big_step_size;
    size_t const small_steps = len % big_step_size;
    unsigned long long *big_ptr1 = (unsigned long long *)src1;
    unsigned long long *big_ptr2 = (unsigned long long *)src2;
    unsigned long long *big_dst = (unsigned long long *)dst;
    for (size_t i = 0; i < big_steps; i++) {
      unsigned long long const x = *big_ptr1;
      unsigned long long const y = *big_ptr2;
      *big_dst = x & y;
      big_ptr1++;
      big_ptr2++;
      big_dst++;
    }
    unsigned char *small_ptr1 = (unsigned char *)big_ptr1;
    unsigned char *small_ptr2 = (unsigned char *)big_ptr2;
    unsigned char *small_dst = (unsigned char *)big_dst;
    for (size_t i = 0; i < small_steps; i++) {
      unsigned char const x = *small_ptr1;
      unsigned char const y = *small_ptr2;
      *small_dst = x & y;
      small_ptr1++;
      small_ptr2++;
      small_dst++;
    }
  }
}

void c_complement_implementation(unsigned char *dst, unsigned char const *src,
                                 size_t const len) {
  size_t const big_step_size = sizeof(unsigned long long);
  size_t const big_steps = len / big_step_size;
  size_t const small_steps = len % big_step_size;
  unsigned long long *big_src = (unsigned long long *)src;
  unsigned long long *big_dst = (unsigned long long *)dst;
  for (size_t i = 0; i < big_steps; i++) {
    unsigned long long const x = *big_src;
    *big_dst = ~x;
    big_src++;
    big_dst++;
  }
  unsigned char *small_src = (unsigned char *)big_src;
  unsigned char *small_dst = (unsigned char *)big_dst;
  for (size_t i = 0; i < small_steps; i++) {
    unsigned char const x = *small_src;
    *small_dst = ~x;
    small_src++;
    small_dst++;
  }
}
