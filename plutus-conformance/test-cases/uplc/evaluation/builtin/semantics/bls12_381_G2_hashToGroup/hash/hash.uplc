-- Check that hashing a random bytestring gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G2_hashToGroup)
   (con bytestring #8e)
  ]
  (con bytestring #0a)
 ]
)