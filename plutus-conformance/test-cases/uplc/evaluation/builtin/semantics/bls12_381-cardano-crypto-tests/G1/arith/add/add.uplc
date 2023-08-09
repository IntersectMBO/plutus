-- Check that adding two random points in G1 gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    (builtin bls12_381_G1_add)
    [
     (builtin bls12_381_G1_uncompress)
     (con bytestring #b93105d0cff4c3f6a42ab790900a26bb1843f4b07fc83d527a66e4a2ddf6c49ea86fe37b1106dbd20dc280ec5996dadf
     )
    ]
    [
     (builtin bls12_381_G1_uncompress)
     (con bytestring #a077246742bfbffdefc1193aba17434d337f231478bf63173065c1e09c34429e76877983ae5f3add1438e5d237f63724
     )
    ]
   ]
  ]
  (con
   bls12_381_G1_element
   0x9863eb0a7f8b092fca1a4333866ae3579ad2a4edef84bfcdf736333b3adf0100820c7603b002bf911b564cf032392f07
  )
 ]
)
