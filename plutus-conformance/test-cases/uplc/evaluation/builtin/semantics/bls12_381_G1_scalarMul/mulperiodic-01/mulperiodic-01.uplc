-- Scalar multiplication by the group size should give you the zero element of the group.
(program 1.0.0
[
 [ (builtin equalsByteString)
  [(builtin bls12_381_G1_compress)
   [
    (builtin bls12_381_G1_scalarMul)
    (con integer 52435875175126190479447740508185965837690552500527637822603658699938581184513 )
    [(builtin bls12_381_G1_uncompress) (con bytestring #abd61864f519748032551e42e0ac417fd828f079454e3e3c9891c5c29ed7f10bdecc046854e3931cb7002779bd76d71f)]
   ]
  ]
 ]
 (con bytestring #c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
]
)
