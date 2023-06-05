-- Check that hashing different messages with the same DST gives different
-- results: this should return False.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    [
     (builtin bls12_381_G1_hashToGroup)
     (con bytestring #8e)
    ]
    (con bytestring #0a)
   ]
  ]
  [
   [
    (builtin bls12_381_G1_hashToGroup)
    (con bytestring #81)
   ]
   (con bytestring #0a)
  ]
 ] 
)