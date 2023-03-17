-- Check that hasing a random bytestring gives the expected result.
(program 1.0.0
 [
  (builtin bls12_381_G2_hashToCurve)
  (con bytestring #3f)
 ]
)