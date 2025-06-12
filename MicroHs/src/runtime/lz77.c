#include <inttypes.h>
#include <stdlib.h>
#if 0
#include <stdio.h>
#define INLINE
#endif

#define MAX(x,y) ((x) > (y) ? (x) : (y))
#define MIN(x,y) ((x) < (y) ? (x) : (y))

#define MAXWIN 8192
#define MAXLEN (9 + 255)
#define MINMATCH 3
#define MINOFFS 1
#define MAXLIT 32

/*
 * Encoding inspired by FastLZ
 *  000nnnnn                      - literal run follows, with n+1 bytes
 *  111ooooo pppppppp nnnnnnnn    - at offset o*256+p, copy n+9 bytes (maximum offset is 8191)
 *  nnnooooo pppppppp             - at offset o*256+p, copy n+2 bytes (n != 0, n != 7)
 * Match length is >= 3.
 */

static void
put(uint8_t **bufp, size_t *sizep, size_t *offsp, uint8_t byte)
{
  if (*offsp >= *sizep) {
    *sizep *= 2;
    *bufp = realloc(*bufp, *sizep);
  }
  (*bufp)[(*offsp)++] = byte;
}
#define PUT(x) put(&outbuf, &outsize, &outoffs, (x))

size_t
lz77d(uint8_t *src, size_t srclen, uint8_t **bufp)
{
  uint8_t *end = src + srclen;
  size_t outsize = 100000;
  uint8_t *outbuf = malloc(outsize);
  size_t outoffs = 0;

  while (src < end) {
    int op = *src++;
    int opx = op & 0x1f;        /* part of offset, or literal length */
    op >>= 5;
    if (op == 0) {
      /* 000nnnnn */
      do {
        PUT(*src++);
      } while (--opx >= 0);
    } else {
      size_t len;
      size_t offs = opx * 256 + *src++ + MINOFFS;
      if (op == 7) {
        /* 111ooooo pppppppp nnnnnnnn */
        len = 9 + *src++;
      } else {
        /* nnnooooo pppppppp */
        len = 2 + op;
      }
      //printf("match cur=%d offs=%d len=%d\n", (int)(dst - adst), (int)offs, (int)len);
      offs = outoffs - offs;
      for (size_t i = 0; i < len; i++) {
        uint8_t b = outbuf[offs + i];
        PUT(b);
      }
    }
  }
  *bufp = outbuf;
  return outoffs;
}

#define HASHBITS 11
#define HASHSIZE (1 << HASHBITS)
typedef size_t lzhash_t;
static INLINE lzhash_t
lz77hash(uint8_t *b, size_t n)
{
#if 0
  n = MIN(n, MINMATCH);
  size_t h = 0;
  for (size_t i = 0; i < n; i++)
    h = h * 256 + b[i];
  return ((h * 99999989) >> 15) & (HASHSIZE - 1);
#else
  n = MIN(n, 4);
  size_t h = 5381;
  for (size_t i = 0; i < n; i++)
    h = h * 33 + b[i];
  return h & (HASHSIZE - 1);
#endif
}

static INLINE size_t
match(uint8_t *src, uint8_t *win, uint8_t *end)
{
  size_t n;

  for(n = 0; *src == *win && src < end && n < MAXLEN; src++, win++, n++)
    ;
  return n;
}

typedef size_t lzoffs_t;
#define NUMPREV 16

/* Find the longest match within the match window */
static INLINE size_t
find_longest_match(uint8_t *src, uint8_t *cur, uint8_t *end, size_t *match_offs_p, lzoffs_t lzhashes[][NUMPREV])
{
  size_t win_end = cur - src + 1;
  size_t win_len = MIN(win_end, MAXWIN);

  lzhash_t h = lz77hash(cur, end - cur);
  lzoffs_t *offsets = lzhashes[h];

  size_t m_len = 0;
  size_t m_offs = 0;
#if 0
  for (size_t offs = MINOFFS; offs < win_len; offs++) {
    size_t n = match(cur, cur - offs, end);
    if (n > m_len) {
      m_len = n;
      m_offs = offs;
    }
  }
#else
  for (size_t i = 0; i < NUMPREV; i++) {
    lzoffs_t o = offsets[i];
    if (o == ~0)
      break;                    /* unused slot */
    size_t offs = (cur - src) - o;
    if (offs >= win_len || offs < MINOFFS)
      break;                  /* offset is not in range */
    size_t n = match(cur, cur - offs, end);
    if (n > m_len) {
      m_len = n;
      m_offs = offs;
    }
  }
#endif
  *match_offs_p = m_offs;
  return m_len;
}

static INLINE void
lzupdatehash(uint8_t *src, uint8_t *cur, uint8_t *end, lzoffs_t lzhashes[][NUMPREV])
{
  lzhash_t h = lz77hash(cur, end - cur);
  lzoffs_t offs = cur - src;

  for(size_t k = NUMPREV-1; k > 0; k--)
    lzhashes[h][k] = lzhashes[h][k-1];
  lzhashes[h][0] = offs;
}


size_t
lz77c(uint8_t *src, size_t srclen, uint8_t **bufp)
{
  uint8_t *cur;
  uint8_t *end = src + srclen;
  size_t outsize = 25000;
  uint8_t *outbuf = malloc(outsize);
  size_t outoffs = 0;

  lzoffs_t lzhashes[HASHSIZE][NUMPREV];

  for(size_t i = 0; i < HASHSIZE; i++) {
    for(size_t k = 0; k < NUMPREV; k++)
      lzhashes[i][k] = ~0;
  }

  for (cur = src; cur < end; ) {
    size_t match_offs = 0;
    size_t match_len = 0;
    size_t len;
    /* Start from the current position and look for a match in the window. */
    /* If the is no match, try the next position, and so on. */
    for (len = 0; len < end - cur; len++) {
      match_len = find_longest_match(src, cur + len, end, &match_offs, lzhashes);
      if (match_len >= MINMATCH) /* Stop when we find a match. */
        break;
      lzupdatehash(src, cur + len, end, lzhashes);
    }
    /* As we exit the loop, we have len bytes that did not match anywhere
     * in the window, so they need to be emitted as a literal. */
    while (len) {
      /* Chunk up the literal into maximum sized pieces. */
      size_t n = MIN(len, MAXLIT);
      PUT(n - 1);               /* Chunk length - 1 */
      for (size_t i = 0; i < n; i++) {
        PUT(*cur++);            /* and spit out the chunk. */
      }
      len -= n;
    }
    if (match_len >= MINMATCH) {
      /* If we actually had a match, output it. */
      //cur += match_len;         /* skip over the matched positions */
      for(size_t i = 0; i < match_len; i++) {
        lzupdatehash(src, cur++, end, lzhashes);
      }
      match_offs -= MINOFFS;
      match_len -= 2;
      int hi = match_offs >> 8;
      int lo = match_offs & 0xff;
      if (match_len < 7) {      /* encode as 2 or 3 bytes */
        PUT((match_len << 5) + hi);
        PUT(lo);
      } else {
        PUT((7 << 5) + hi);
        PUT(lo);
        PUT(match_len - 7);
      }
    }
  }
  *bufp = outbuf;
  return outoffs;
}

#if 0
int
main(int argc, char **argv)
{
  FILE *fi = fopen(argv[1], "r");
  FILE *fo = fopen(argv[2], "w");
  int dec = argc > 3;
  fseek(fi, 0, SEEK_END);
  size_t ilen = ftell(fi);
  size_t olen;
  fseek(fi, 0, SEEK_SET);
  uint8_t *ibuf = malloc(ilen);
  uint8_t *obuf;
  size_t n = fread(ibuf, 1, ilen, fi);
  if (n != ilen) exit(1);
  if (dec)
    olen = lz77d(ibuf, ilen, &obuf);
  else
    olen = lz77c(ibuf, ilen, &obuf);
  fwrite(obuf, olen, 1, fo);
  exit(0);
}
#endif
