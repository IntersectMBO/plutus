#ifndef HMAC_H
#define HMAC_H

#include "cryptonite_sha512.h"

#define HMAC_CTX(_name) HMAC_ ## _name ## _ctx
#define HMAC_INIT(_name) HMAC_ ## _name ## _init
#define HMAC_UPDATE(_name) HMAC_ ## _name ## _update
#define HMAC_FINAL(_name) HMAC_ ## _name ## _final

#define DECL_HMAC(_name, _blocksz, _hashsz, _ctx, _init, _update, _final)     \
  typedef struct {                                                            \
    _ctx inner;                                                               \
    _ctx outer;                                                               \
  } HMAC_CTX(_name);                                                          \
                                                                              \
  static inline void HMAC_INIT(_name)(HMAC_CTX(_name) *ctx,                   \
                                      const uint8_t *key, size_t nkey)        \
  {                                                                           \
    /* Prepare key: */                                                        \
    uint8_t k[_blocksz];                                                      \
    uint8_t blk_inner[_blocksz];                                              \
    uint8_t blk_outer[_blocksz];                                              \
    size_t i;                                                                 \
                                                                              \
    /* Shorten long keys. */                                                  \
    if (nkey > _blocksz)                                                      \
    {                                                                         \
      _init(&ctx->inner);                                                     \
      _update(&ctx->inner, key, nkey);                                        \
      _final(&ctx->inner, k);                                                 \
                                                                              \
      key = k;                                                                \
      nkey = _hashsz;                                                         \
    }                                                                         \
                                                                              \
    /* Standard doesn't cover case where blocksz < hashsz. */                 \
    assert(nkey <= _blocksz);                                                 \
                                                                              \
    /* Right zero-pad short keys. */                                          \
    if (k != key)                                                             \
      memcpy(k, key, nkey);                                                   \
    if (_blocksz > nkey)                                                      \
      memset(k + nkey, 0, _blocksz - nkey);                                   \
                                                                              \
    /* Start inner hash computation */                                        \
    for (i = 0; i < _blocksz; i++)                                            \
    {                                                                         \
      blk_inner[i] = 0x36 ^ k[i];                                             \
      blk_outer[i] = 0x5c ^ k[i];                                             \
    }                                                                         \
                                                                              \
    _init(&ctx->inner);                                                       \
    _update(&ctx->inner, blk_inner, sizeof blk_inner);                        \
                                                                              \
    /* And outer. */                                                          \
    _init(&ctx->outer);                                                       \
    _update(&ctx->outer, blk_outer, sizeof blk_outer);                        \
  }                                                                           \
                                                                              \
  static inline void HMAC_UPDATE(_name)(HMAC_CTX(_name) *ctx,                 \
                                        const void *data, size_t ndata)       \
  {                                                                           \
    _update(&ctx->inner, data, ndata);                                        \
  }                                                                           \
                                                                              \
  static inline void HMAC_FINAL(_name)(HMAC_CTX(_name) *ctx,                  \
                                       uint8_t out[_hashsz])                  \
  {                                                                           \
    _final(&ctx->inner, out);                                                 \
    _update(&ctx->outer, out, _hashsz);                                       \
    _final(&ctx->outer, out);                                                 \
  }


#endif
