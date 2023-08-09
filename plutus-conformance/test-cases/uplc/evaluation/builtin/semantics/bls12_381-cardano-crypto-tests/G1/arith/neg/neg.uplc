-- Check that negating a random point in G1 gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    (builtin bls12_381_G1_neg)
    [
     (builtin bls12_381_G1_uncompress)
     (con bytestring #b93105d0cff4c3f6a42ab790900a26bb1843f4b07fc83d527a66e4a2ddf6c49ea86fe37b1106dbd20dc280ec5996dadf)
    ]
   ]
  ]
  (con
   bls12_381_G1_element
   0x993105d0cff4c3f6a42ab790900a26bb1843f4b07fc83d527a66e4a2ddf6c49ea86fe37b1106dbd20dc280ec5996dadf
  )
 ]
)
