#ifndef CBITS_H
#define CBITS_H

#include <stdbool.h>
#include <stddef.h>

// Popcount

size_t c_popcount_naive(unsigned char const *restrict src, size_t const len);

size_t c_popcount_block(unsigned char const *restrict src, size_t len);

size_t c_popcount_block_unroll(unsigned char const *restrict src, size_t len);

// Complement

void c_complement_naive(unsigned char *restrict dst,
                        unsigned char const *restrict src, size_t const len);

// Homogeneity

bool c_homogenous_naive(unsigned char const needle,
                        unsigned char const *restrict haystack,
                        size_t const len);

bool c_homogenous_sliding_window(unsigned char const needle,
                                 unsigned char const *restrict haystack,
                                 size_t len);

// Binary ops

void c_and_naive(unsigned char *restrict dst, unsigned char const *src1,
                 unsigned char const *src2, size_t const len);

// Bit reading and writing

bool c_bit_at(size_t const ix, unsigned char *const restrict src);

void c_bit_set_naive(bool const b, size_t const ix, unsigned char *restrict dst,
                     unsigned char const *restrict src, size_t const len);

void c_bit_set_memcpy(bool const b, size_t const ix,
                      unsigned char *restrict dst,
                      unsigned char const *restrict src, size_t const len);

// CLZ

size_t c_clz_naive(unsigned char const *restrict src, size_t const len);

size_t c_clz_block(unsigned char const *restrict src, size_t len);

size_t c_clz_block_unrolled(unsigned char const *restrict src, size_t len);

#endif /* CBITS_H */
