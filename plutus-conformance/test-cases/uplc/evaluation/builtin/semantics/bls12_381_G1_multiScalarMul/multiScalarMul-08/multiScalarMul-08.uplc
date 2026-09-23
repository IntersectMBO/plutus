-- Both arguments are empty lists => result = zero
(program 1.0.0
 [(builtin bls12_381_G1_equal)
  [(builtin bls12_381_G1_multiScalarMul)
   (con (list integer) [])
   (con (list bls12_381_G1_element) [])
  ]
  [(builtin bls12_381_G1_uncompress) (con bytestring #c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)]
 ]
)
