-- Test vector (0-bit input) for Blake2b_224.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin blake2b_224)
    (con bytestring #)
   ]
  ]
 (con bytestring #836cc68931c2e4e3e838602eca1902591d216837bafddfe6f0c8cb07)
 ]
)
