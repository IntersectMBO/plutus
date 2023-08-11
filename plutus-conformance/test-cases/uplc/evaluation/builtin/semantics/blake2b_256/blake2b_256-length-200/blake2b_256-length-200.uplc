-- Test vector (200-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin blake2b_256)
    (con bytestring #2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200)
   ]
  ]
 (con bytestring #91c60f99b33303c02b39ed93b713e3915a180c3747f3b31e05727618ee401624)
 ]
)
