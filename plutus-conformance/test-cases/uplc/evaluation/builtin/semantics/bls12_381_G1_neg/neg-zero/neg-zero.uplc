-- The negative of the zero point is the zero point.
(program 1.0.0
 [(builtin bls12_381_G1_compress) [
  (builtin bls12_381_G1_neg)
  [(builtin bls12_381_G1_uncompress) (con bytestring #c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
 ]]
)
