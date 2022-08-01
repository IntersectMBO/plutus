#ifndef CBITS_H
#define CBITS_H

#include <stddef.h>

void c_and_implementation(unsigned char *dst, unsigned char const *src1,
                          unsigned char const *src2, size_t const len);

void c_and_implementation_3(unsigned char *dst, unsigned char const *src1,
                            unsigned char const *src2, size_t const len);

#endif /* CBITS_H */
