-- This has the infinity bit set but not the compression bit, and so is invalid.
(program 0.0.0
 [
  (builtin bls12_381_G1_uncompress)
  (con bytestring  #400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
 ]
)