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
    h$cardano_crypto.HEAPU8[tgt+i] = u8[buf_o+i];
    hexes += h$toHex(u8[buf_o+i]);
  }
  // h$logWrapper("=> " + len + " " + hexes + " " + buf_o + " " + buf_d.len);
}

function h$copyFromHeap(src, buf_d, buf_o, len) {
  var u8 = buf_d.u8;
  var hexes = "";
  for(var i=0;i<len;i++) {
    u8[buf_o+i] = h$cardano_crypto.HEAPU8[src+i];
    hexes += h$toHex(h$cardano_crypto.HEAPU8[src+i]);
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
      h$cardano_crypto._free(h$buffers[n]);
    }
    h$buffers[n] = h$cardano_crypto._malloc(2*minSize); // fixme 2* shouldn't be needed
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


/* ED25519 */
var h$ed25519_pk_size      = 32;
var h$ed25519_sk_size      = 64;
var h$ed25519_sig_size     = 64;

function h$cardano_crypto_ed25519_sign_open(m_d, m_o, mlen, pk_d, pk_o, sig_d, sig_o) {
  h$logWrapper("h$cardano_crypto_ed25519_sign_open");
  var m_ptr   = h$getTmpBufferWith(0, m_d,   m_o,   mlen),
      pk_ptr  = h$getTmpBufferWith(1, pk_d,  pk_o,  h$ed25519_pk_size),
      sig_ptr = h$getTmpBufferWith(2, sig_d, sig_o, h$ed25519_sig_size);
  return h$cardano_crypto._cardano_crypto_ed25519_sign_open(m_ptr, mlen, pk_ptr, sig_ptr);
}

function h$cardano_crypto_ed25519_sign(m_d, m_o, mlen, salt_d, salt_o, slen, sk_d, sk_o, pk_d, pk_o, sig_d, sig_o) {
  h$logWrapper("h$cardano_crypto_ed25519_sign");
  var m_ptr    = h$getTmpBufferWith(0, m_d, m_o, mlen),
      salt_ptr = h$getTmpBufferWith(1, salt_d, salt_o, slen),
      sk_ptr   = h$getTmpBufferWith(2, sk_d, sk_o, h$ed25519_sk_size),
      pk_ptr   = h$getTmpBufferWith(3, pk_d, pk_o, h$ed25519_pk_size),
      sig_ptr  = h$getTmpBuffer(4, h$ed25519_sig_size);
  h$cardano_crypto._cardano_crypto_ed25519_sign
             (m_ptr, mlen, salt_ptr, slen, sk_ptr, pk_ptr, sig_ptr);
  h$copyFromHeap(sig_ptr, sig_d, sig_o, h$ed25519_sig_size);
}

function h$cardano_crypto_ed25519_publickey(sk_d, sk_o, pk_d, pk_o) {
  h$logWrapper("h$cardano_crypto_ed25519_publickey");
  var sk_ptr = h$getTmpBufferWith(0, sk_d, sk_o, h$ed25519_sk_size),
      pk_ptr = h$getTmpBuffer(1, h$ed25519_pk_size);
  h$cardano_crypto._cardano_crypto_ed25519_publickey(sk_ptr, pk_ptr);
  h$copyFromHeap(pk_ptr, pk_d, pk_o, h$ed25519_pk_size);
}

function h$cardano_crypto_ed25519_point_add(pk1_d, pk1_o, pk2_d, pk2_o, res_d, res_o) {
  h$logWrapper("h$cardano_crypto_ed25519_point_add");
  var pk1_ptr = h$getTmpBufferWith(0, pk1_d, pk1_o, h$ed25519_pk_size),
      pk2_ptr = h$getTmpBufferWith(1, pk2_d, pk2_o, h$ed25519_pk_size),
      res_ptr = h$getTmpBuffer(2, h$ed25519_pk_size);
  var r = h$cardano_crypto._cardano_crypto_ed25519_point_add(pk1_ptr, pk2_ptr, res_ptr);
  h$copyFromHeap(res_ptr, res_d, res_o, h$ed25519_pk_size);
  return r;
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
  var r = h$cardano_crypto._wallet_encrypted_derive_public(pub_in_ptr, cc_in_ptr, index, pub_out_ptr, cc_out_ptr, mode);
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
  h$cardano_crypto._wallet_encrypted_derive_private(in_ptr, pass_ptr, pass_len, index, out_ptr, mode);
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
  h$cardano_crypto._wallet_encrypted_sign(ec_ptr, pass_ptr, pass_len, data_ptr, data_len, sig_ptr);
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
  var r = h$cardano_crypto._wallet_encrypted_from_secret(pass_ptr, pass_len, seed_ptr, cc_ptr, ec_ptr);
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
  h$cardano_crypto._wallet_encrypted_change_pass(in_ptr, old_pass_ptr, old_pass_len, new_pass_ptr, new_pass_len, out_ptr);
  h$copyFromHeap(out_ptr, out_d, out_o, h$full_key_size);
}

function h$wallet_encrypted_new_from_mkg( pass_d, pass_o, pass_len
                                        , master_key_d, master_key_o
                                        , encrypted_key_d, encrypted_key_o) {
  h$logWrapper("h$wallet_encrypted_new_from_mkg");
  var pass_ptr      = h$getTmpBufferWith(0, pass_d, pass_o, pass_len),
      master_ptr    = h$getTmpBufferWith(1, master_key_d, master_key_o, h$master_key_size),
      encrypted_ptr = h$getTmpBuffer(2, h$full_key_size);
  var r = h$cardano_crypto._wallet_encrypted_new_from_mkg(pass_ptr, pass_len, master_ptr, encrypted_ptr);
  h$copyFromHeap(encrypted_ptr, encrypted_key_d, encrypted_key_o, h$full_key_size);
  return r;
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
  return -19; // ENODEV; foundation returns the same for non-linux hosts.
}
