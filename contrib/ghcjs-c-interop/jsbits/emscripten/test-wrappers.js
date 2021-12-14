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

function h$test_fold(stbl_buf, stbl_ptr, n) {
  var f = h$deRefStablePtr(stbl_ptr);
      fptr = h$ghcjs_c_interop.addFunction(f)
      ret = h$ghcjs_c_interop._test_fold(fptr, n);
  h$ghcjs_c_interop.removeFunction(fptr);
  return ret;
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
