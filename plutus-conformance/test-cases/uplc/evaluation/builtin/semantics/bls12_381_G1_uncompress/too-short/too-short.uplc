-- The bytestring is the compressed version of the G1 zero point, but truncated to 47 bytes.
(program 0.0.0
 [
  (builtin bls12_381_G1_uncompress)
  (con bytestring #c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
 ]
)