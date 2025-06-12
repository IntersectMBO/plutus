
/***************** BFILE *******************/
/*
 * BFILE is a family of stream objects.
 * There are two kinds: endpoints (source/sink) and transducers.
 * The streams are typically bytes.
 *
 *  FILE   source/sink for stdio FILE handles
 *  buf    source/sink where the read/write uses a memory buffer.
 *
 *  lz77   transducer for LZ77 compression
 *         put - compresses a byte
 *         get - returns an decompressed byte
 *  rle    transducer for Run Length Encoding
 *         put - compresses an ASCII character
 *         get - returns a decompressed ASCII
 *  bwt    transducer for Burrows-Wheeler Transform
 *         put - transforms a byte
 *         get - untransforms a byte
 *  utf8   transducer for UTF8 encoding
 *         put - encodes a Unicode code point (int) to bytes
 *         get - decodes a Unicode code point
 */

/**** Buffers for collecting data. */

struct bfbuffer {
  size_t   size;                /* total size of buffer */
  size_t   pos;                 /* current index into buffer */
  uint8_t *buf;                 /* actual data */
};

void
bfbuffer_init(struct bfbuffer *bf, size_t size)
{
  bf->size = size;
  bf->pos = 0;
  bf->buf = MALLOC(size);
  if (!bf->buf)
    ERR("bfbuffer_init");
}

int
bfbuffer_get(struct bfbuffer *bf)
{
  if (bf->pos >= bf->size)
    return -1;
  return bf->buf[bf->pos++];
}

void
bfbuffer_snoc(struct bfbuffer *bf, int byte)
{
  if (bf->pos >= bf->size) {
    bf->size *= 2;
    bf->buf = REALLOC(bf->buf, bf->size);
    if (!bf->buf)
      ERR("bfbuffer_snoc");
  }
  bf->buf[bf->pos++] = byte;
}

size_t
bfbuffer_read(struct bfbuffer *bf, uint8_t *buf, size_t size)
{
  if (bf->pos + size > bf->size) {
    size = bf->size - bf->pos;
  }
  memcpy(buf, bf->buf + bf->pos, size);
  bf->pos += size;
  return size;
}

size_t
bfbuffer_write(struct bfbuffer *bf, const uint8_t *str, size_t size)
{
  if (bf->pos + size > bf->size) {
    do {
      bf->size *= 2;
    } while (bf->pos + size > bf->size);
    bf->buf = REALLOC(bf->buf, bf->size);
    if (!bf->buf)
      ERR("bfbuffer_write");
  }
  memcpy(bf->buf + bf->pos, str, size);
  bf->pos += size;
  return size;
}

void
bfbuffer_free(struct bfbuffer *bf)
{
  FREE(bf->buf);
}

/*********************************/

/* Sanity checking */
#define CHECKBFILE(p, f) do { if (p->getb != f) { ERR("CHECKBFILE"); } } while(0)

/* BFILE will have different implementations, they all have these methods */
typedef struct BFILE {
  int (*getb)(struct BFILE*);
  void (*ungetb)(int, struct BFILE*);
  void (*putb)(int, struct BFILE*);
  void (*flushb)(struct BFILE*);
  void (*closeb)(struct BFILE*);
  size_t (*readb)(uint8_t *, size_t, struct BFILE*); /* optional block read */
  size_t (*writeb)(const uint8_t *, size_t, struct BFILE*); /* optional block write */
} BFILE;

static INLINE int
getb(BFILE *p)
{
  return p->getb(p);
}

static INLINE void
ungetb(int c, BFILE *p)
{
  p->ungetb(c, p);
}

static INLINE void
putb(int c, BFILE *p)
{
  p->putb(c, p);
}

static INLINE void
closeb(BFILE *p)
{
  p->closeb(p);
}

static INLINE void
flushb(BFILE *p)
{
  p->flushb(p);
}

void
putsb(const char *str, struct BFILE *p)
{
  char c;
  while ((c = *str++))
    putb(c, p);
}

size_t
readb(uint8_t *buf, size_t size, BFILE *p)
{
  if (p->readb) {
    /* If there is a read method, use it. */
    return p->readb(buf, size, p);
  } else {
    /* Otherwise, do it byte by byte. */
    size_t s;
    for (s = 0; s < size; s++) {
      int c = getb(p);
      if (c < 0)
        break;
      buf[s] = c;
    }
    return s;
  }
}

size_t
writeb(const uint8_t *str, size_t size, BFILE *p)
{
  if (p->writeb) {
    /* If there is a write method, use it. */
    return p->writeb(str, size, p);
  } else {
    /* Otherwise, do it byte by byte. */
    size_t s;
    for(s = 0; s < size; s++) {
      putb(str[s], p);
    }
    return s;
  }
}

/* convert -n to a string, handles MINBOUND correctly */
void
putnegb(value_t n, BFILE *p)
{
  int c = '0' - n % 10;
  if (n <= -10) {
    putnegb(n / 10, p);
  }
  putb(c, p);
}

void
putdecb(value_t n, BFILE *p)
{
  if (n < 0) {
    putb('-', p);
    putnegb(n, p);
  } else {
    putnegb(-n, p);
  }
}

void
putint32(value_t n, BFILE *p)
{
  putb(n % 256, p); n /= 256;
  putb(n % 256, p); n /= 256;
  putb(n % 256, p); n /= 256;
  putb(n % 256, p);
}

value_t
getint32(BFILE *p)
{
  value_t b0 = getb(p);
  value_t b1 = getb(p);
  value_t b2 = getb(p);
  value_t b3 = getb(p);
  return ((((b3 * 256) + b2) * 256) + b1) * 256 + b0;
}

/***************** BFILE from/to memory buffer *******************/
struct BFILE_buffer {
  BFILE    mets;
  struct bfbuffer bf;
};

int
getb_buf(BFILE *bp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);

  return bfbuffer_get(&p->bf);
}

void
putb_buf(int c, BFILE *bp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);

  bfbuffer_snoc(&p->bf, c);
}

void
ungetb_buf(int c, BFILE *bp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);
  if (p->bf.pos == 0)
    ERR("ungetb");
  p->bf.buf[--p->bf.pos] = (uint8_t)c;
}

void
closeb_rd_buf(BFILE *bp)
{
  CHECKBFILE(bp, getb_buf);
  FREE(bp);
}

void
closeb_wr_buf(BFILE *bp)
{
  CHECKBFILE(bp, getb_buf);
  FREE(bp);
}

void
flushb_buf(BFILE *bp)
{
  CHECKBFILE(bp, getb_buf);
}

size_t
readb_buf(uint8_t *buf, size_t size, BFILE *bp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);

  return bfbuffer_read(&p->bf, buf, size);
}

size_t
writeb_buf(const uint8_t *str, size_t size, BFILE *bp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);

  return bfbuffer_write(&p->bf, str, size);
}

struct BFILE*
openb_rd_buf(uint8_t *buf, size_t len)
{
  struct BFILE_buffer *p = MALLOC(sizeof(struct BFILE_buffer));
  if (!p)
    memerr();
  p->mets.getb = getb_buf;
  p->mets.ungetb = ungetb_buf;
  p->mets.putb = 0;
  p->mets.flushb = 0;
  p->mets.closeb = closeb_rd_buf;
  p->mets.readb = readb_buf;
  p->mets.writeb = 0;
  p->bf.size = len;
  p->bf.pos = 0;
  p->bf.buf = buf;
  return (struct BFILE*)p;
}

struct BFILE*
openb_wr_buf(void)
{
  struct BFILE_buffer *p = MALLOC(sizeof(struct BFILE_buffer));
  if (!p)
    memerr();
  p->mets.getb = getb_buf;      /* Just to make CHECKFILE happy */
  p->mets.ungetb = 0;
  p->mets.putb = putb_buf;
  p->mets.flushb = flushb_buf;
  p->mets.closeb = closeb_wr_buf;
  p->mets.readb = 0;
  p->mets.writeb = writeb_buf;
  bfbuffer_init(&p->bf, 1000);
  return (struct BFILE*)p;
}

/*
 * Get the buffer used by writing.
 * This should be the last operation before closing,
 * since the buffer can move when writing.
 * The caller of openb_wr_buf() and get_buf() owns
 * the memory and must free it.
 */
void
get_buf(struct BFILE *bp, uint8_t **bufp, size_t *lenp)
{
  struct BFILE_buffer *p = (struct BFILE_buffer *)bp;
  CHECKBFILE(bp, getb_buf);
  *bufp = p->bf.buf;
  *lenp = p->bf.pos;
}

#if WANT_STDIO
/***************** BFILE via FILE *******************/
struct BFILE_file {
  BFILE    mets;
  FILE    *file;
};

int
getb_file(BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  return fgetc(p->file);
}

void
ungetb_file(int c, BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  ungetc(c, p->file);
}

void
putb_file(int c, BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  (void)fputc(c, p->file);
}

void
flushb_file(BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  fflush(p->file);
}

void
closeb_file(BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  fclose(p->file);
  FREE(p);
}

void
freeb_file(BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  FREE(p);
}

size_t
readb_file(uint8_t *buf, size_t size, BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  return fread(buf, 1, size, p->file);
}

size_t
writeb_file(const uint8_t *str, size_t size, BFILE *bp)
{
  struct BFILE_file *p = (struct BFILE_file *)bp;
  CHECKBFILE(bp, getb_file);
  return fwrite(str, 1, size, p->file);
}

BFILE *
add_FILE(FILE *f)
{
  struct BFILE_file *p = MALLOC(sizeof (struct BFILE_file));
  if (!p)
    memerr();
  p->mets.getb   = getb_file;
  p->mets.ungetb = ungetb_file;
  p->mets.putb   = putb_file;
  p->mets.flushb = flushb_file;
  p->mets.closeb = closeb_file;
  p->mets.readb  = readb_file;
  p->mets.writeb = writeb_file;
  p->file = f;
  return (BFILE*)p;
}
#endif


#if WANT_LZ77
/***************** BFILE via simple LZ77 decompression *******************/
struct BFILE_lz77 {
  BFILE    mets;
  BFILE    *bfile;              /* underlying BFILE */
  struct bfbuffer bf;
  int      read;
  int      numflush;
};

int
getb_lz77(BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77*)bp;
  CHECKBFILE(bp, getb_lz77);

  return bfbuffer_get(&p->bf);
}

void
ungetb_lz77(int c, BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77*)bp;
  CHECKBFILE(bp, getb_lz77);
  p->bf.pos--;
}

void
putb_lz77(int b, BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77*)bp;
  CHECKBFILE(bp, getb_lz77);

  bfbuffer_snoc(&p->bf, b);
}

/* Compress and write to output BFILE */
void
flushb_lz77(BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77*)bp;
  CHECKBFILE(bp, getb_lz77);

  /* If we have had a flush, and there is no new data then do nothing */
  if (p->numflush++ && !p->bf.pos)
    return;
  uint8_t *obuf;
  size_t olen = lz77c(p->bf.buf, p->bf.pos, &obuf);
  putsb("LZ1", p->bfile);              /* Version no */
  putint32(olen, p->bfile);            /* 32 bit length */
  for (size_t i = 0; i < olen; i++) {
    putb(obuf[i], p->bfile);           /* and the data */
  }
  FREE(obuf);
  p->bf.pos = 0;
  flushb(p->bfile);
}

void
closeb_lz77(BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77*)bp;
  CHECKBFILE(bp, getb_lz77);

  if (!p->read) {
    /* We are in write mode, so compress and push it down */
    flushb_lz77(bp);
    bfbuffer_free(&p->bf);
  }

  closeb(p->bfile);
  FREE(p);
}

size_t
readb_lz77(uint8_t *buf, size_t size, BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77 *)bp;
  CHECKBFILE(bp, getb_lz77);

  return bfbuffer_read(&p->bf, buf, size);
}

size_t
writeb_lz77(const uint8_t *str, size_t size, BFILE *bp)
{
  struct BFILE_lz77 *p = (struct BFILE_lz77 *)bp;
  CHECKBFILE(bp, getb_lz77);

  return bfbuffer_write(&p->bf, str, size);
}

BFILE *
add_lz77_decompressor(BFILE *file)
{
  struct BFILE_lz77 *p = MALLOC(sizeof(struct BFILE_lz77));

  if (!p)
    memerr();
  memset(p, 0, sizeof(struct BFILE_lz77));
  p->mets.getb = getb_lz77;
  p->mets.ungetb = ungetb_lz77;
  p->mets.putb = 0;
  p->mets.flushb = 0;
  p->mets.closeb = closeb_lz77;
  p->mets.readb = readb_lz77;
  p->mets.writeb = 0;
  p->read = 1;
  p->bfile = file;
  p->numflush = 0;

  /* First check version */
  if (getb(file) != 'L' || getb(file) != 'Z' || getb(file) != '1')
    ERR("Bad LZ77 signature");

  size_t size = getint32(file); /* then read size */
  uint8_t *buf = MALLOC(size);  /* temporary buffer for input */
  if (!buf)
    memerr();
  for(size_t i = 0; i < size; i++) {
    buf[i] = getb(file);        /* and read data */
  }
  p->bf.size = lz77d(buf, size, &p->bf.buf); /* decompress */
  FREE(buf);
  p->bf.pos = 0;
  return (BFILE*)p;
}

BFILE *
add_lz77_compressor(BFILE *file)
{
  struct BFILE_lz77 *p = MALLOC(sizeof(struct BFILE_lz77));

  if (!p)
    memerr();
  memset(p, 0, sizeof(struct BFILE_lz77));
  p->mets.getb = getb_lz77;
  p->mets.ungetb = 0;
  p->mets.putb = putb_lz77;
  p->mets.flushb = flushb_lz77;
  p->mets.closeb = closeb_lz77;
  p->mets.readb = 0;
  p->mets.writeb = writeb_lz77;
  p->read = 0;
  p->bfile = file;
  p->numflush = 0;

  bfbuffer_init(&p->bf, 25000);
  return (BFILE*)p;
}

#endif  /* WANT_LZ77 */

#if WANT_RLE
/***************** BFILE via RLE decompression *******************/
/*
 * Run Length Encoding for ASCII
 * Format
 * c                -  c         one ASCII character
 * 0x80+n c         -  n+1       repetitions of ASCII character c, n>1
 * 0x80+n 0x80+m c  -  n*128+m+1 repetitions of ASCII character c
 * ... for longer run lengths
 * Non-ASCII (i.e., >= 128) have very poor encoding:
 * 0x81 c-0x80
 */

struct BFILE_rle {
  BFILE    mets;
  BFILE    *bfile;              /* underlying BFILE */
  size_t   count;
  int      byte;
  int      unget;
  int      read;
};

int
get_rep(BFILE *in)
{
  size_t n = 0;
  for(;;) {
    int c = getb(in);
    //fprintf(stderr,"get_rep %02x\n", c);
    if (c < 0)
      return -1;
    if (c < 128) {
      ungetb(c, in);
      return n;
    }
    n = n * 128 + c - 128;
  }
}

int
getb_rle(BFILE *bp)
{
  struct BFILE_rle *p = (struct BFILE_rle*)bp;
  CHECKBFILE(bp, getb_rle);
  if (p->unget >= 0) {
    int c = p->unget;
    p->unget = -1;
    return c;
  }
  if (p->count) {
    p->count--;
    return p->byte;
  } else {
    int n = get_rep(p->bfile);
    if (n < 0) {
      return -1;
    } else if (n == 1) {
      /* repetition count == 1 means a non-ASCII byte */
      return getb(p->bfile) | 0x80;
    } else {
      p->count = n;
      p->byte = getb(p->bfile);
      return p->byte;
    }
  }
}

void
ungetb_rle(int c, BFILE *bp)
{
  struct BFILE_rle *p = (struct BFILE_rle*)bp;
  CHECKBFILE(bp, getb_rle);
  p->unget = c;
}

void
put_rep(BFILE *out, size_t n)
{
  if (n > 127)
    put_rep(out, n / 128);
  putb(n % 128 + 128, out);
}

void
out_rle(struct BFILE_rle *p)
{
  if (p->count > 2) {
    /* More than 2 repeating chars, it's worth compressing */
    put_rep(p->bfile, p->count - 1);
    putb(p->byte, p->bfile);
  } else {
    while(p->count-- > 0)
      putb(p->byte, p->bfile);
  }
}

void
putb_rle(int b, BFILE *bp)
{
  struct BFILE_rle *p = (struct BFILE_rle*)bp;
  CHECKBFILE(bp, getb_rle);

  if (b & 0x80) {
    /* Encode non-ASCII as repetition count 1, followed by the byte with MSB removed */
    out_rle(p);
    put_rep(p->bfile, 1);
    putb(b & 0x7f, p->bfile);
    p->count = 0;
    p->byte = -1;
  } else if (b == p->byte) {
    p->count++;
  } else {
    out_rle(p);
    p->count = 1;
    p->byte = b;
  }
}

void
closeb_rle(BFILE *bp)
{
  struct BFILE_rle *p = (struct BFILE_rle*)bp;
  CHECKBFILE(bp, getb_rle);

  if (!p->read)
    flushb(bp);

  closeb(p->bfile);
}

void
flushb_rle(BFILE *bp)
{
  struct BFILE_rle *p = (struct BFILE_rle*)bp;
  CHECKBFILE(bp, getb_rle);

  /* output last byte(s) */
  out_rle(p);
  p->count = 0;
  flushb(p->bfile);
}

BFILE *
add_rle_decompressor(BFILE *file)
{
  struct BFILE_rle *p = MALLOC(sizeof(struct BFILE_rle));

  if (!p)
    memerr();
  p->mets.getb = getb_rle;
  p->mets.ungetb = ungetb_rle;
  p->mets.putb = 0;
  p->mets.flushb = 0;
  p->mets.closeb = closeb_rle;
  p->mets.readb = 0;
  p->mets.writeb = 0;
  p->count = 0;
  p->unget = -1;
  p->bfile = file;
  p->read = 1;

  return (BFILE*)p;
}

BFILE *
add_rle_compressor(BFILE *file)
{
  struct BFILE_rle *p = MALLOC(sizeof(struct BFILE_rle));

  if (!p)
    memerr();
  p->mets.getb = getb_rle;
  p->mets.ungetb = 0;
  p->mets.putb = putb_rle;
  p->mets.flushb = flushb_rle;
  p->mets.closeb = closeb_rle;
  p->mets.readb = 0;
  p->mets.writeb = 0;
  p->count = 0;
  p->byte = -1;
  p->bfile = file;
  p->read = 0;

  return (BFILE*)p;
}

#endif  /* WANT_RLE */

#if WANT_BWT
/***************** BFILE via Burrows-Wheeler Transform *******************/
/*
 */

struct BFILE_bwt {
  BFILE    mets;
  BFILE    *bfile;              /* underlying BFILE */
  size_t   count;
  struct bfbuffer bf;
  int      read;
  int      numflush;
};

int
getb_bwt(BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt*)bp;
  CHECKBFILE(bp, getb_bwt);

  return bfbuffer_get(&p->bf);
}

void
ungetb_bwt(int c, BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt*)bp;
  CHECKBFILE(bp, getb_bwt);
  p->bf.pos--;
}

void
putb_bwt(int b, BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt*)bp;
  CHECKBFILE(bp, getb_bwt);

  bfbuffer_snoc(&p->bf, b);
}

void
closeb_bwt(BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt*)bp;
  CHECKBFILE(bp, getb_bwt);

  if (!p->read)
    flushb(bp);

  closeb(p->bfile);
}

size_t
readb_bwt(uint8_t *buf, size_t size, BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt *)bp;
  CHECKBFILE(bp, getb_bwt);

  return bfbuffer_read(&p->bf, buf, size);
}

size_t
writeb_bwt(const uint8_t *str, size_t size, BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt *)bp;
  CHECKBFILE(bp, getb_bwt);

  return bfbuffer_write(&p->bf, str, size);
}

/* Sort all rotations of buf, and the indices of the sorted strings in res. */
/*
 * |.......................................|
 *         ^           ^
 *         a           b
 *                     <-      n         ->
 *         <-  m     ->
 * <-  o ->
 */
static uint8_t *compar_arg;
static size_t compar_len;
int compar(const void *pa, const void *pb)
{
  uint32_t a = *(uint32_t*)pa;
  uint32_t b = *(uint32_t*)pb;
  int r;
  if (a == b)
    return 0;
  if (a < b) {
    size_t n = compar_len - b; /* bytes until end of buffer */
    r = memcmp(compar_arg + a, compar_arg + b, n);
    if (r)
      return r;
    size_t m = b - a;
    r = memcmp(compar_arg + a + n, compar_arg, m);
    if (r)
      return r;
    size_t o = a;
    return memcmp(compar_arg, compar_arg + m, o);
  } else {
    size_t n = compar_len - a; /* bytes until end of buffer */
    r = memcmp(compar_arg + a, compar_arg + b, n);
    if (r)
      return r;
    size_t m = a - b;
    r = memcmp(compar_arg, compar_arg + b + n, m);
    if (r)
      return r;
    size_t o = a;
    return memcmp(compar_arg + m, compar_arg, o);

  }
  return 0;
}

void
sort_buffer(uint8_t *buf, size_t buflen, uint32_t *res)
{
  for(size_t i = 0; i < buflen; i++)
    res[i] = i;
  compar_arg = buf;
  compar_len = buflen;
  qsort(res, buflen, sizeof(uint32_t), compar);
}

uint32_t
encode_bwt(uint8_t *data, size_t len, uint8_t *last)
{
  uint32_t *res = MALLOC(len * sizeof(uint32_t));
  if (!res)
    ERR("encode_bwt");
  sort_buffer(data, len, res);
  uint32_t zero = 0;
  for(size_t i = 0; i < len; i++) {
    uint32_t offs = res[i];
    last[i] = data[(offs + len - 1) % len];
    if (offs == 0)
      zero = i;
  }
  FREE(res);
  return zero;
}

void
flushb_bwt(BFILE *bp)
{
  struct BFILE_bwt *p = (struct BFILE_bwt*)bp;
  CHECKBFILE(bp, getb_bwt);

  /* If we have had a flush, and there is no new data then do nothing */
  if (p->numflush++ && !p->bf.pos)
    return;
  putsb("BW1", p->bfile);             /* version no */
  putint32(p->bf.pos, p->bfile);      /* 32 bit length */
  uint8_t *last = MALLOC(p->bf.pos);
  if (!last)
    ERR("flushb_bwt");
  size_t zero = encode_bwt(p->bf.buf, p->bf.pos, last);
  putint32(zero, p->bfile);
  for(size_t i = 0; i < p->bf.pos; i++)
    putb(last[i], p->bfile);
  FREE(last);
  p->bf.pos = 0;
  flushb(p->bfile);
}

#define MAX_BYTE 256

void
decode_bwt(uint8_t *data, size_t len, uint8_t *odata, size_t zero)
{
  size_t count[MAX_BYTE];
  uint32_t *pred = MALLOC(len * sizeof(uint32_t));
  for(size_t i = 0; i < MAX_BYTE; i++) {
    count[i] = 0;
  }
  for(size_t i = 0; i < len; i++) {
    pred[i] = count[data[i]]++;
  }
  size_t sum = 0;
  for(size_t i = 0; i < MAX_BYTE; i++) {
    size_t s = count[i];
    count[i] = sum;
    sum += s;
  }
  size_t i = zero;
  for(size_t j = len; j > 0; j--) {
    odata[j - 1] = data[i];
    i = pred[i] + count[data[i]];
  }
  FREE(pred);
}

BFILE *
add_bwt_decompressor(BFILE *file)
{
  struct BFILE_bwt *p = MALLOC(sizeof(struct BFILE_bwt));

  if (!p)
    memerr();
  memset(p, 0, sizeof(struct BFILE_bwt));
  p->mets.getb = getb_bwt;
  p->mets.ungetb = ungetb_bwt;
  p->mets.putb = 0;
  p->mets.flushb = 0;
  p->mets.closeb = closeb_bwt;
  p->mets.readb = readb_bwt;
  p->mets.writeb = 0;
  p->read = 1;
  p->bfile = file;
  p->numflush = 0;

  /* First check version */
  if (getb(file) != 'B' || getb(file) != 'W' || getb(file) != '1')
    ERR("Bad BWT signature");

  size_t size = getint32(file); /* then read size */
  uint32_t zero = getint32(file);

  uint8_t *buf = MALLOC(size);  /* temporary buffer for input */
  if (!buf)
    memerr();
  for(size_t i = 0; i < size; i++) {
    buf[i] = getb(file);        /* and read data */
  }
  bfbuffer_init(&p->bf, size);
  decode_bwt(buf, size, p->bf.buf, zero); /* decode */
  FREE(buf);

  return (BFILE*)p;
}

BFILE *
add_bwt_compressor(BFILE *file)
{
  struct BFILE_bwt *p = MALLOC(sizeof(struct BFILE_bwt));

  if (!p)
    memerr();
  p->mets.getb = getb_bwt;
  p->mets.ungetb = 0;
  p->mets.putb = putb_bwt;
  p->mets.flushb = flushb_bwt;
  p->mets.closeb = closeb_bwt;
  p->mets.readb = 0;
  p->mets.writeb = writeb_bwt;
  p->read = 0;
  p->bfile = file;
  p->numflush = 0;

  bfbuffer_init(&p->bf, 25000);
  return (BFILE*)p;
}

#endif  /* WANT_BWT */

/***************** BFILE with UTF8 encode/decode *******************/

struct BFILE_utf8 {
  BFILE    mets;
  BFILE    *bfile;
  int      unget;
};

/* XXX: This is not right with WORD_SIZE==16 */
int
getb_utf8(BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8*)bp;
  CHECKBFILE(bp, getb_utf8);
  int c1, c2, c3, c4;

  /* Do we have an ungetb character? */
  if (p->unget >= 0) {
    c1 = p->unget;
    p->unget = -1;
    return c1;
  }
  c1 = getb(p->bfile);
  if (c1 < 0)
    return -1;
  if ((c1 & 0x80) == 0)
    return c1;
  c2 = getb(p->bfile);
  if (c2 < 0)
    return -1;
  if ((c1 & 0xe0) == 0xc0) {
    int c = ((c1 & 0x1f) << 6) | (c2 & 0x3f);
    if (c < 0x80) ERR("getb_utf8: overlong encoding");
    return c;
  }
  c3 = getb(p->bfile);
  if (c3 < 0)
    return -1;
  if ((c1 & 0xf0) == 0xe0) {
    int c = ((c1 & 0x0f) << 12) | ((c2 & 0x3f) << 6) | (c3 & 0x3f);
    if (c < 0x800) ERR("getb_utf8: overlong encoding");
    return c;
  }
  c4 = getb(p->bfile);
  if (c4 < 0)
    return -1;
  if ((c1 & 0xf8) == 0xf0) {
    int c = ((c1 & 0x07) << 18) | ((c2 & 0x3f) << 12) | ((c3 & 0x3f) << 6) | (c4 & 0x3f);
    if (c < 0x10000) ERR("getb_utf8: overlong encoding");
    return c;
  }
  ERR("getb_utf8");
}

void
ungetb_utf8(int c, BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8*)bp;
  CHECKBFILE(bp, getb_utf8);
  if (p->unget >= 0)
    ERR("ungetb_utf8");
  p->unget = c;
}

void
putb_utf8(int c, BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8 *)bp;
  CHECKBFILE(bp, getb_utf8);
  if (c < 0)
    ERR("putb_utf8: < 0");
  if (c < 0x80) {
    putb(c, p->bfile);
    return;
  }
  if (c < 0x800) {
    putb(((c >> 6 )       ) | 0xc0, p->bfile);
    putb(((c      ) & 0x3f) | 0x80, p->bfile);
    return;
  }
  if (c < 0x10000) {
    putb(((c >> 12)       ) | 0xe0, p->bfile);
    putb(((c >> 6 ) & 0x3f) | 0x80, p->bfile);
    putb(((c      ) & 0x3f) | 0x80, p->bfile);
    return;
  }
  if (c < 0x110000) {
    putb(((c >> 18)       ) | 0xf0, p->bfile);
    putb(((c >> 12) & 0x3f) | 0x80, p->bfile);
    putb(((c >> 6 ) & 0x3f) | 0x80, p->bfile);
    putb(((c      ) & 0x3f) | 0x80, p->bfile);
    return;
  }
  ERR("putb_utf8");
}

void
flushb_utf8(BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8*)bp;
  CHECKBFILE(bp, getb_utf8);

  flushb(p->bfile);
}

void
closeb_utf8(BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8*)bp;
  CHECKBFILE(bp, getb_utf8);

  closeb(p->bfile);
  FREE(p);
}

size_t
readb_utf8(uint8_t *buf, size_t size, BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8 *)bp;
  CHECKBFILE(bp, getb_utf8);

  return readb(buf, size, p->bfile);
}

size_t
writeb_utf8(const uint8_t *str, size_t size, BFILE *bp)
{
  struct BFILE_utf8 *p = (struct BFILE_utf8 *)bp;
  CHECKBFILE(bp, getb_utf8);

  return writeb(str, size, p->bfile);
}

BFILE *
add_utf8(BFILE *file)
{
  struct BFILE_utf8 *p = MALLOC(sizeof(struct BFILE_utf8));

  if (!p)
    memerr();
  p->mets.getb = getb_utf8;
  p->mets.ungetb = ungetb_utf8;
  p->mets.putb = putb_utf8;
  p->mets.flushb = flushb_utf8;
  p->mets.closeb = closeb_utf8;
  p->mets.readb = readb_utf8;
  p->mets.writeb = writeb_utf8;
  p->bfile = file;
  p->unget = -1;

  return (BFILE*)p;
}
