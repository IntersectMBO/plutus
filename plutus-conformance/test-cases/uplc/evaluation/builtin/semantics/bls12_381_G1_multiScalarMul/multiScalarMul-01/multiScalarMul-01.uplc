-- Multi-scalar multiplication is the same as ordinary scalar multiplication for inputs of size 1.
(program 1.0.0
 [(builtin bls12_381_G1_equal)
  [(builtin bls12_381_G1_multiScalarMul)
   (con (list integer) [-7843724524521392138901923801823923123123454352157])
   [ (force (builtin mkCons))
  [(builtin bls12_381_G1_uncompress) (con bytestring #950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)]
  (con (list bls12_381_G1_element) [])
]
  ]
  [(builtin bls12_381_G1_scalarMul)
   (con integer -7843724524521392138901923801823923123123454352157)
   [(builtin bls12_381_G1_uncompress) (con bytestring #950dfd33da2682260c76038dfb8bad6e84ae9d599a3c151815945ac1e6ef6b1027cd917f3907479d20d636ce437a41f5)]
  ]
 ]
)
