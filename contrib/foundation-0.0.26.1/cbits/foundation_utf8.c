#include <stdint.h>
#include <stdlib.h>
#include "foundation_prim.h"

#if 0
static const uint64_t utf8_mask_80 = 0x8080808080808080ULL;
static const uint64_t utf8_mask_40 = 0x4040404040404040ULL;

typedef unsigned long pu;
#define POPCOUNT(x) __builtin_popcountl(x)
#define ALIGNED8(p) ((((uintptr_t) (p)) & (sizeof(pu)-1)) == 0)

FsCountOf foundation_utf8_length(uint8_t *p8, const FsOffset start_offset, const FsOffset end_offset)
{
    const uint8_t *end = p8 + end_offset;
    FsCountOf n = 0;

    p8 += start_offset;

    while (!ALIGNED8(p8) && p8 < end) {
        if ((*p8++ & 0xc0) != 0x80) { n++; }
    }

    /* process 8 bytes */
    for (; (p8 + sizeof(pu)) <= end; p8 += sizeof(pu)) {
        pu h   = *((pu *) p8);
        pu h80 = h & utf8_mask_80;

        /* only ASCII */
        if (h80 == 0) {
            n += sizeof(pu);
            continue;
        }

        int nb_ascii = (h80 == utf8_mask_80) ? 0 : (8 - __builtin_popcountl(h80));
        int nb_high = __builtin_popcountl( h & (h80 >> 1));
        n += nb_ascii + nb_high;
    }

    while (p8 < end) {
        if ((*p8++ & 0xc0) != 0x80) { n++; }
    }

    return n;
}

#define IS_CONT(x) ((x & 0xc0) == 0x80)

int foundation_utf8_validate(const uint8_t *c, size_t offset, size_t end)
{
    while (offset < end) {
        uint8_t h = c[offset];
        if (!(h & 0x80)) {
            offset++;
            continue;
        }

        /* continuation */
        if      (h < 0xC0) { goto fail1; }
        /* 2 bytes */
        else if (h < 0xE0) { if      (offset + 1 >= end) { goto fail2; }
            else if (IS_CONT(c[offset+1])) { offset += 2; }
            else { goto fail1; }
        }
        /* 3 bytes */
        else if (h < 0xF0) { if      (offset + 2 >= end) { goto fail2; }
            else if (IS_CONT(c[offset+1]) && IS_CONT(c[offset+2])) { offset += 3; }
            else { goto fail1; }
        }

        /* 4 bytes */
        else if (h < 0xFE) { if      (offset + 3 >= end) { goto fail2; }
            else if (IS_CONT(c[offset+1]) && IS_CONT(c[offset+2]) && IS_CONT(c[offset+3])) { offset += 4; }
            else { goto fail1; }
        }
        /* invalid > 4 bytes */
        else               { goto fail1; }
    }
    return 0;
fail1:
    return 1;
fail2:
    return 2;
}
#endif
