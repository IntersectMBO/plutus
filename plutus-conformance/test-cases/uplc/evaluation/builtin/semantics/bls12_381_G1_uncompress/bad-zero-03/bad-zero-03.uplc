-- This is the zero point of G1, but with a random bit set in the body.  It
-- should fail to uncompress.
(program 0.0.0
 [
  (builtin bls12_381_G1_uncompress)
  (con bytestring #c00000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000)
 ]
)