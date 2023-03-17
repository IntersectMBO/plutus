-- This is the zero point of G1, but with the sign bit set.  It should fail to uncompress.
(program 0.0.0
 [
  (builtin bls12_381_G1_uncompress)
  (con bytestring #e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
 ]
)
 