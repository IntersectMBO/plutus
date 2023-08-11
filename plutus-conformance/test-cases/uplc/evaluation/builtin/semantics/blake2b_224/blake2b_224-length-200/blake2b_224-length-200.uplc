-- Test vector (200-bit input) for Blake2b_224.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin blake2b_224)
    (con bytestring #2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200)
   ]
  ]
 (con bytestring #93d4b80c531998973b08297fc5042af359865a8702f20b5fc2db8df5)
 ]
)
