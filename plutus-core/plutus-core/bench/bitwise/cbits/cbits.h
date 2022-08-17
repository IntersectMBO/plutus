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

// Others

void c_and_implementation_naive(unsigned char *dst, unsigned char const *src1,
                                unsigned char const *src2, size_t const len);

void c_and_implementation(unsigned char *dst, unsigned char const *src1,
                          unsigned char const *src2, size_t const len);

void c_and_implementation_3(unsigned char *dst, unsigned char const *src1,
                            unsigned char const *src2, size_t const len);

#endif /* CBITS_H */
