/*
  Pointers in emscripten compiled code are represented as offsets
  into the global HEAP ArrayBuffer.

  GHCJS pointers (Addr#) and unlifted arrays (ByteArray# etc.) are represented
  as a pair of a buffer and an offset.
 */

function h$logWrapper(x) {
  /* console.log(x); */
}

function h$copyToHeap(buf_d, buf_o, tgt, len) {
  if(len === 0) return;
  var u8 = buf_d.u8;
  var hexes = "";
  for(var i=0;i<len;i++) {
    h$cryptonite.HEAPU8[tgt+i] = u8[buf_o+i];
    hexes += h$toHex(u8[buf_o+i]);
  }
  // h$logWrapper("=> " + len + " " + hexes + " " + buf_o + " " + buf_d.len);
}

function h$copyFromHeap(src, buf_d, buf_o, len) {
  var u8 = buf_d.u8;
  var hexes = "";
  for(var i=0;i<len;i++) {
    u8[buf_o+i] = h$cryptonite.HEAPU8[src+i];
    hexes += h$toHex(h$cryptonite.HEAPU8[src+i]);
  }
  // h$logWrapper("<= " + len + " " + hexes + " " + buf_o + " " + buf_d.len);
}

function h$toHex(n) {
  var s = n.toString(16);
  if(s.length === 1) s = '0' + s;
  return s;
}

var h$buffers     = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];
var h$bufferSizes = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0];

function h$getTmpBuffer(n, minSize) {
  var sn = h$bufferSizes[n];
  if(sn < minSize) {
    if(sn > 0) {
      h$cryptonite._free(h$buffers[n]);
    }
    h$buffers[n] = h$cryptonite._malloc(2*minSize); // fixme 2* shouldn't be needed
    h$bufferSizes[n] = minSize;
  }
  return h$buffers[n];
}

function h$getTmpBufferWith(n, buf_d, buf_o, len) {
  // fixme: we can avoid the copying if the buffer is already the actual
  //        heap buffer
  var buf_ptr = h$getTmpBuffer(n, len);
  h$copyToHeap(buf_d, buf_o, buf_ptr, len);
  return buf_ptr;
}

/* MD5 */
var h$md5_ctx_size         = 76; // fixme test
var h$md5_digest_size      = 16;

function h$cryptonite_md5_init(ctx_d, ctx_o) {
  h$logWrapper("h$cryptonite_md5_init");
  var ctx_ptr = h$getTmpBuffer(0, h$md5_ctx_size);
  h$cryptonite._cryptonite_md5_init(ctx_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$md5_ctx_size);
}

function h$cryptonite_md5_update(ctx_d, ctx_o, data_d, data_o, len) {
  h$logWrapper("h$cryptonite_md5_update");
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d,  ctx_o,  h$md5_ctx_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, len);
  h$cryptonite._cryptonite_md5_update(ctx_ptr, data_ptr, len);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$md5_ctx_size);
}

function h$cryptonite_md5_finalize(ctx_d, ctx_o, out_d, out_o) {
  h$logWrapper("h$cryptonite_md5_finalize");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$md5_ctx_size),
      out_ptr = h$getTmpBuffer(1, h$md5_digest_size);
  h$cryptonite._cryptonite_md5_finalize(ctx_ptr, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, h$md5_digest_size);
}

/* SHA256 */
var h$sha256_ctx_size      = 192; // 168;
var h$sha256_digest_size   = 32;

function h$cryptonite_sha256_init(ctx_d, ctx_o) {
  h$logWrapper("h$cryptonite_sha256_init");
  var ctx_ptr = h$getTmpBuffer(0, h$sha256_ctx_size);
  h$cryptonite._cryptonite_sha256_init(ctx_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$sha256_ctx_size);
}

function h$cryptonite_sha256_update(ctx_d, ctx_o, data_d, data_o, len) {
  h$logWrapper("h$cryptonite_sha256_update");
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d,  ctx_o,  h$sha256_ctx_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, len);
  h$cryptonite._cryptonite_sha256_update(ctx_ptr, data_ptr, len);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$sha256_ctx_size);
}

function h$cryptonite_sha256_finalize(ctx_d, ctx_o, out_d, out_o) {
  h$logWrapper("h$cryptonite_sha256_finalize");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$sha256_ctx_size),
      out_ptr = h$getTmpBuffer(1, h$sha256_digest_size);
  h$cryptonite._cryptonite_sha256_finalize(ctx_ptr, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, h$sha256_digest_size);
}

/* SHA512 */
var h$sha512_ctx_size      = 256; // 208; // 256?
var h$sha512_digest_size   = 64;

function h$cryptonite_sha512_init(ctx_d, ctx_o) {
  h$logWrapper("h$cryptonite_sha512_init");
  var ctx_ptr = h$getTmpBuffer(0, h$sha512_ctx_size);
  h$cryptonite._cryptonite_sha512_init(ctx_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$sha512_ctx_size);
}

function h$cryptonite_sha512_update(ctx_d, ctx_o, data_d, data_o, len) {
  h$logWrapper("h$cryptonite_sha512_update");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$sha512_ctx_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, len);
  h$cryptonite._cryptonite_sha512_update(ctx_ptr, data_ptr, len);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$sha512_ctx_size);
}

function h$cryptonite_sha512_finalize(ctx_d, ctx_o, out_d, out_o) {
  h$logWrapper("h$cryptonite_sha512_finalize");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$sha512_ctx_size),
      out_ptr = h$getTmpBuffer(1, h$sha512_digest_size);
  h$cryptonite._cryptonite_sha512_finalize(ctx_ptr, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, h$sha512_digest_size);
}

/* SHA3 */

/*
  SHA3 has a variable digest size, which affects the size of the context.

  Rather than figuring out exactly how much is needed, we just copy a bit
  more data back and forth, up to the maximum context and diegest size,
  while ensuring that we don't overrun our ArrayBuffer
 */
var h$sha3_ctx_size_max    = 376; // maximum size
var h$sha3_digest_size_max = 64;  // maximum size

function h$cryptonite_sha3_init(ctx_d, ctx_o, hashlen) {
  h$logWrapper("h$cryptonite_sha3_init");
  var ctx_size = Math.min(h$sha3_ctx_size_max, ctx_d.len-ctx_o);
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d, ctx_o, ctx_size);
  h$cryptonite._cryptonite_sha3_init(ctx_ptr, hashlen);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, ctx_size);
}

function h$cryptonite_sha3_update(ctx_d, ctx_o, data_d, data_o, len) {
  h$logWrapper("h$cryptonite_sha3_update");
  var ctx_size = Math.min(h$sha3_ctx_size_max, ctx_d.len-ctx_o);
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, ctx_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, len);
  h$cryptonite._cryptonite_sha3_update(ctx_ptr, data_ptr, len);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, ctx_size);
}

function h$cryptonite_sha3_finalize(ctx_d, ctx_o, hashlen, out_d, out_o) {
  h$logWrapper("h$cryptonite_sha3_finalize");
  var ctx_size = Math.min(h$sha3_ctx_size_max, ctx_d.len-ctx_o);
     //  digest_size = Math.min(h$sha3_digest_size_max,out_d.len-out_o);
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, ctx_size),
      out_ptr = h$getTmpBufferWith(1, out_d, out_o, hashlen / 8);
  h$cryptonite._cryptonite_sha3_finalize(ctx_ptr, hashlen, out_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, ctx_size);
  h$copyFromHeap(out_ptr, out_d, out_o, hashlen / 8);
}

/* BLAKE2B */

var h$blake2b_state_size = 248; // fixme, this number may be wrong for different hash sizes than the wallet uses

function h$cryptonite_blake2b_init(ctx_d, ctx_o, hashlen) {
  h$logWrapper("h$cryptonite_blake2b_init");
  var ctx_ptr = h$getTmpBuffer(0, ctx_d, ctx_o, h$blake2b_state_size);
  h$cryptonite._cryptonite_blake2b_init(ctx_ptr, hashlen);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$blake2b_state_size);
}

function h$cryptonite_blake2b_update(ctx_d, ctx_o, data_d, data_o, len) {
  h$logWrapper("h$cryptonite_blake2b_update");
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d, ctx_o, h$blake2b_state_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, len);
  h$cryptonite._cryptonite_blake2b_update(ctx_ptr, data_ptr, len);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$blake2b_state_size);
}

function h$cryptonite_blake2b_finalize(ctx_d, ctx_o, hashlen, out_d, out_o) {
  h$logWrapper("h$cryptonite_blake2b_finalize");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$blake2b_state_size),
      out_ptr = h$getTmpBuffer(1, hashlen);
  h$cryptonite._cryptonite_blake2b_finalize(ctx_ptr, hashlen, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, hashlen);
}

/* ED25519 */
var h$ed25519_pk_size      = 32;
var h$ed25519_sk_size      = 64;
var h$ed25519_sig_size     = 64;

function h$cryptonite_ed25519_point_base_scalarmul(r_d, r_o, s_d, s_o) {
  h$logWrapper("h$cardano_crypto_ed25519_point_base_scalarmul");
  // XXX sizes
  var s_ptr = h$getTmpBufferWith(0, s_d, s_o, 40),
      r_ptr = h$getTmpBuffer(1, 160);
  h$cryptonite._cryptonite_ed25519_point_base_scalarmul(r_ptr, s_ptr);
  h$copyFromHeap(r_ptr, r_d, r_o, 160);
}

function h$cryptonite_ed25519_point_encode(out_d, out_o, in_d, in_o) {
    // XXX sizes
    h$logWrapper("h$cardano_crypto_ed25519_point_encode");
    var in_ptr = h$getTmpBufferWith(0, in_d, in_o, 160),
        out_ptr = h$getTmpBuffer(1, 32);
    h$cryptonite._cryptonite_ed25519_point_encode(out_ptr, in_ptr);
    h$copyFromHeap(out_ptr, out_d, out_o, 32);
}

function h$cryptonite_ed25519_scalar_decode_long(out_d, out_o, in_d, in_o, len) {
  h$logWrapper("h$cardano_crypto_ed25519_decode_long");
  // XXX sizes
  var in_ptr = h$getTmpBufferWith(0, in_d, in_o, len),
      out_ptr = h$getTmpBuffer(1, 40);
  var r = h$cryptonite._cryptonite_ed25519_scalar_decode_long(out_ptr, in_ptr, len);
  h$copyFromHeap(out_ptr, out_d, out_o, 40);
  return r;
}

function h$cryptonite_ed25519_sign_open(m_d, m_o, mlen, pk_d, pk_o, sig_d, sig_o) {
  h$logWrapper("h$cryptonite_ed25519_sign_open");
  var m_ptr   = h$getTmpBufferWith(0, m_d,   m_o,   mlen),
      pk_ptr  = h$getTmpBufferWith(1, pk_d,  pk_o,  h$ed25519_pk_size),
      sig_ptr = h$getTmpBufferWith(2, sig_d, sig_o, h$ed25519_sig_size);
  return h$cryptonite._cryptonite_ed25519_sign_open(m_ptr, mlen, pk_ptr, sig_ptr);
}

function h$cryptonite_ed25519_sign(m_d, m_o, mlen, salt_d, salt_o, slen, sk_d, sk_o, pk_d, pk_o, sig_d, sig_o) {
  h$logWrapper("h$cryptonite_ed25519_sign");
  var m_ptr    = h$getTmpBufferWith(0, m_d, m_o, mlen),
      salt_ptr = h$getTmpBufferWith(1, salt_d, salt_o, slen),
      sk_ptr   = h$getTmpBufferWith(2, sk_d, sk_o, h$ed25519_sk_size),
      pk_ptr   = h$getTmpBufferWith(3, pk_d, pk_o, h$ed25519_pk_size),
      sig_ptr  = h$getTmpBuffer(4, h$ed25519_sig_size);
  h$cryptonite._cryptonite_ed25519_sign
             (m_ptr, mlen, salt_ptr, slen, sk_ptr, pk_ptr, sig_ptr);
  h$copyFromHeap(sig_ptr, sig_d, sig_o, h$ed25519_sig_size);
}

function h$cryptonite_ed25519_publickey(sk_d, sk_o, pk_d, pk_o) {
  h$logWrapper("h$cryptonite_ed25519_publickey");
  var sk_ptr = h$getTmpBufferWith(0, sk_d, sk_o, h$ed25519_sk_size),
      pk_ptr = h$getTmpBuffer(1, h$ed25519_pk_size);
  h$cryptonite._cryptonite_ed25519_publickey(sk_ptr, pk_ptr);
  h$copyFromHeap(pk_ptr, pk_d, pk_o, h$ed25519_pk_size);
}

function h$cryptonite_ed25519_point_add(pk1_d, pk1_o, pk2_d, pk2_o, res_d, res_o) {
  h$logWrapper("h$cryptonite_ed25519_point_add");
  var pk1_ptr = h$getTmpBufferWith(0, pk1_d, pk1_o, h$ed25519_pk_size),
      pk2_ptr = h$getTmpBufferWith(1, pk2_d, pk2_o, h$ed25519_pk_size),
      res_ptr = h$getTmpBuffer(2, h$ed25519_pk_size);
  var r = h$cryptonite._cryptonite_ed25519_point_add(pk1_ptr, pk2_ptr, res_ptr);
  h$copyFromHeap(res_ptr, res_d, res_o, h$ed25519_pk_size);
  return r;
}

/* pbkdf */

function h$cryptonite_fastpbkdf2_hmac_sha512( pw_d, pw_o, pw_len
                                            , salt_d, salt_o, salt_len
                                            , iterations
                                            , out_d, out_o, out_len) {
  h$logWrapper("h$cryptonite_fastpbkdf2_hmac_sha512");
  var pw_ptr   = h$getTmpBufferWith(0, pw_d, pw_o, pw_len),
      salt_ptr = h$getTmpBufferWith(1, salt_d, salt_o, salt_len),
      out_ptr  = h$getTmpBuffer(2, out_len);
  h$cryptonite._cryptonite_fastpbkdf2_hmac_sha512(pw_ptr, pw_len, salt_ptr, salt_len, iterations, out_ptr, out_len);
  h$copyFromHeap(out_ptr, out_d, out_o, out_len);
}

/* wallet stuff */
var h$secret_key_seed_size = 32;
var h$chain_code_size = 32;
var h$public_key_size = 32;
var h$master_key_size = 96;
var h$encrypted_key_size = 64;
var h$full_key_size = h$encrypted_key_size + h$public_key_size + h$chain_code_size;

function h$wallet_encrypted_derive_public( pub_in_d, pub_in_o
                                         , cc_in_d, cc_in_o
                                         , index
                                         , pub_out_d, pub_out_o
                                         , cc_out_d, cc_out_o
                                         , mode) {
  h$logWrapper("h$wallet_encrypted_derive_public");
  var pub_in_ptr  = h$getTmpBufferWith(0, pub_in_d, pub_in_o, h$public_key_size),
      cc_in_ptr   = h$getTmpBufferWith(1, cc_in_d, cc_in_o, h$chain_code_size),
      pub_out_ptr = h$getTmpBuffer(2, h$public_key_size),
      cc_out_ptr  = h$getTmpBuffer(3, h$chain_code_size);
  var r = h$cryptonite._wallet_encrypted_derive_public(pub_in_ptr, cc_in_ptr, index, pub_out_ptr, cc_out_ptr, mode);
  h$copyFromHeap(pub_out_ptr, pub_out_d, pub_out_o, h$public_key_size);
  h$copyFromHeap(cc_out_ptr, cc_out_d, cc_out_o, h$chain_code_size);
  return r;
}

function h$wallet_encrypted_derive_private( in_d, in_o,
                                            pass_d, pass_o, pass_len,
                                            index,
                                            out_d, out_o,
                                            mode
                                          ) {
  h$logWrapper("h$wallet_encrypted_derive_private");
  // console.log(arguments);
  var in_ptr = h$getTmpBufferWith(0, in_d, in_o, h$full_key_size),
      pass_ptr = h$getTmpBufferWith(1, pass_d, pass_o, pass_len),
      out_ptr  = h$getTmpBuffer(2, h$full_key_size);
  h$cryptonite._wallet_encrypted_derive_private(in_ptr, pass_ptr, pass_len, index, out_ptr, mode);
  h$copyFromHeap(out_ptr, out_d, out_o, h$full_key_size);
}

function h$wallet_encrypted_sign( encrypted_key_d, encrypted_key_o
                                , pass_d, pass_o, pass_len
                                , data_d, data_o, data_len
                                , sig_d, sig_o) {
  h$logWrapper("h$wallet_encrypted_sign");
  var ec_ptr   = h$getTmpBufferWith(0, encrypted_key_d, encrypted_key_o, h$full_key_size),
      pass_ptr = h$getTmpBufferWith(1, pass_d, pass_o, pass_len),
      data_ptr = h$getTmpBufferWith(2, data_d, data_o, data_len),
      sig_ptr  = h$getTmpBuffer(3, h$ed25519_sig_size);
  h$cryptonite._wallet_encrypted_sign(ec_ptr, pass_ptr, pass_len, data_ptr, data_len, sig_ptr);
  h$copyFromHeap(sig_ptr, sig_d, sig_o, h$ed25519_sig_size);
}

function h$wallet_encrypted_from_secret( pass_d, pass_o, pass_len
                                       , seed_d, seed_o
                                       , cc_d, cc_o
                                       , encrypted_key_d, encrypted_key_o
                                       ) {
  h$logWrapper("h$wallet_encrypted_from_secret");
  var pass_ptr = h$getTmpBufferWith(0, pass_d, pass_o, pass_len),
      seed_ptr = h$getTmpBufferWith(1, seed_d, seed_o, h$secret_key_seed_size),
      cc_ptr   = h$getTmpBufferWith(2, cc_d, cc_o, h$chain_code_size),
      ec_ptr   = h$getTmpBufferWith(3, encrypted_key_d, encrypted_key_o, h$full_key_size);
  var r = h$cryptonite._wallet_encrypted_from_secret(pass_ptr, pass_len, seed_ptr, cc_ptr, ec_ptr);
  h$copyFromHeap(ec_ptr, encrypted_key_d, encrypted_key_o, h$full_key_size);
  return r;
}

function h$wallet_encrypted_change_pass( in_d, in_o
                                       , old_pass_d, old_pass_o, old_pass_len
                                       , new_pass_d, new_pass_o, new_pass_len
                                       , out_d, out_o) {
  h$logWrapper("h$wallet_encrypted_change_pass");
  var in_ptr       = h$getTmpBufferWith(0, in_d, in_o, h$full_key_size),
      old_pass_ptr = h$getTmpBufferWith(1, old_pass_d, old_pass_o, old_pass_len),
      new_pass_ptr = h$getTmpBufferWith(2, new_pass_d, new_pass_o, new_pass_len),
      out_ptr      = h$getTmpBuffer(3, h$full_key_size);
  h$cryptonite._wallet_encrypted_change_pass(in_ptr, old_pass_ptr, old_pass_len, new_pass_ptr, new_pass_len, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, h$full_key_size);
}

function h$wallet_encrypted_new_from_mkg( pass_d, pass_o, pass_len
                                        , master_key_d, master_key_o
                                        , encrypted_key_d, encrypted_key_o) {
  h$logWrapper("h$wallet_encrypted_new_from_mkg");
  var pass_ptr      = h$getTmpBufferWith(0, pass_d, pass_o, pass_len),
      master_ptr    = h$getTmpBufferWith(1, master_key_d, master_key_o, h$master_key_size),
      encrypted_ptr = h$getTmpBuffer(2, h$full_key_size);
  var r = h$cryptonite._wallet_encrypted_new_from_mkg(pass_ptr, pass_len, master_ptr, encrypted_ptr);
  h$copyFromHeap(encrypted_ptr, encrypted_key_d, encrypted_key_o, h$full_key_size);
  return r;
}

/* chacha */
var h$chacha_ctx_size = 132;
var h$chacha_state_size = 64;

function h$cryptonite_chacha_generate(dst_d, dst_o, ctx_d, ctx_o, bytes) {
  h$logWrapper("h$cryptonite_chacha_generate");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$chacha_ctx_size),
      dst_ptr = h$getTmpBuffer(1, bytes);
  h$cryptonite._cryptonite_chacha_generate(dst_ptr, ctx_ptr, bytes);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$chacha_ctx_size);
  h$copyFromHeap(dst_ptr, dst_d, dst_o, bytes);
}

function h$cryptonite_chacha_combine(dst_d, dst_o, ctx_d, ctx_o, src_d, src_o, bytes) {
  h$logWrapper("h$cryptonite_chacha_generate");
  var ctx_ptr = h$getTmpBufferWith(0, ctx_d, ctx_o, h$chacha_ctx_size),
      src_ptr = h$getTmpBufferWith(1, src_d, src_o, bytes),
      dst_ptr = h$getTmpBuffer(2, bytes);
  h$cryptonite._cryptonite_chacha_combine(dst_ptr, ctx_ptr, src_ptr, bytes);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$chacha_ctx_size);
  h$copyFromHeap(dst_ptr, dst_d, dst_o, bytes);
}

function h$cryptonite_chacha_init( ctx_d, ctx_o, nb_rounds, keylen, key_d, key_o, ivlen, iv_d, iv_o) {
  var key_ptr = h$getTmpBufferWith(0, key_d, key_o, keylen),
      iv_ptr  = h$getTmpBufferWith(1, iv_d, iv_o, ivlen),
      ctx_ptr = h$getTmpBuffer(2, h$chacha_ctx_size);
  h$cryptonite._cryptonite_chacha_init(ctx_ptr, nb_rounds, keylen, key_ptr, ivlen, iv_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$chacha_ctx_size);
}

function h$cryptonite_chacha_random( rounds, dst_d, dst_o, st_d, st_o, bytes) {
  var dst_ptr = h$getTmpBufferWith(0, dst_d, dst_o, bytes);
      st_ptr  = h$getTmpBufferWith(1, st_d, st_o, h$chacha_state_size);
  h$cryptonite._cryptonite_chacha_random( rounds, dst_ptr, st_ptr, bytes);
  // we might have modified the state.
  h$copyFromHeap(st_ptr, st_d, st_o, h$chacha_state_size);
  h$copyFromHeap(dst_ptr, dst_d, dst_o, bytes);
}

function h$cryptonite_chacha_init_core( st_d, st_o, keylen, key_d, key_o, ivlen, iv_d, iv_o) {
  var key_ptr = h$getTmpBufferWith(0, key_d, key_o, keylen),
      iv_ptr  = h$getTmpBufferWith(1, iv_d, iv_o, ivlen),
      st_ptr = h$getTmpBuffer(2, h$chacha_state_size);
  h$cryptonite._cryptonite_chacha_init_core(st_ptr, keylen, key_ptr, ivlen, iv_ptr);
  h$copyFromHeap(st_ptr, st_d, st_o, h$chacha_state_size);
}



/* poly1305 */
var h$poly1305_ctx_size = 88;
var h$poly1305_key_size = 32;
var h$poly1305_mac_size = 16;

function h$cryptonite_poly1305_init(ctx_d, ctx_o, key_d, key_o) {
  var ctx_ptr  = h$getTmpBuffer(0, h$poly1305_ctx_size),
      key_ptr  = h$getTmpBufferWith(1, key_d, key_o, h$poly1305_key_size);
  h$cryptonite._cryptonite_poly1305_init(ctx_ptr, key_ptr);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$poly1305_ctx_size);
}

function h$cryptonite_poly1305_update(ctx_d, ctx_o, data_d, data_o, length) {
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d, ctx_o, h$poly1305_ctx_size),
      data_ptr = h$getTmpBufferWith(1, data_d, data_o, length >>> 0);
  h$cryptonite._cryptonite_poly1305_update(ctx_ptr, data_ptr, length);
  h$copyFromHeap(ctx_ptr, ctx_d, ctx_o, h$poly1305_ctx_size);
}

function h$cryptonite_poly1305_finalize(mac8_d, mac8_o, ctx_d, ctx_o) {
  var ctx_ptr  = h$getTmpBufferWith(0, ctx_d, ctx_o, h$poly1305_ctx_size),
      mac8_ptr = h$getTmpBuffer(1, h$poly1305_mac_size);
  h$cryptonite._cryptonite_poly1305_finalize(mac8_ptr, ctx_ptr);
  h$copyFromHeap(mac8_ptr, mac8_d, mac8_o, h$poly1305_mac_size);
}

// temporary fixes

// XXX fix this in thrunner.js probably
if(typeof __dirname == 'undefined') {
  var __dirname = '/';
}

// TODO: remove
// TODO: stub, add real implementation
function h$geteuid() {
  return 1;
}

// TODO: stub, add real implementation
function h$sysconf() {
  return 0;
}

// TODO: stub, add real implementation
function h$getpwuid_r(uid, pwd_d, pwd_o, buf_d, buf_o, buflen, result_d, result_o) {
  var i, name = h$encodeUtf8("user"), max = Math.min(72, pwd_d.len);
  if(!result_d.arr) result_d.arr = [];
  result_d.arr[0] = [pwd_d, pwd_o];
  if(!pwd_d.arr) pwd_d.arr = [];
  // we don't really know where the pointers to strings are supposed to go,
  // so we just point to our dummy string everywhere
  for(i = 0; i < max; i+=4) pwd_d.arr[i+pwd_o] = [name, 0];
  for(i = 0; i < (max>>2); i++) pwd_d.i3[i+(pwd_o>>2)] = 1;
  return 0;
}

// TODO: move to foundation
function h$foundation_sysrandom_linux(buf_d, buf_o, size) {
  cryptoObj.getRandomValues(typedArray);
}
