-- Scalar multiplication gives the correct result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    [
     (builtin bls12_381_G1_scalarMul)
     (con integer 29342537169447282925541144552701591957563885683358707334406144036950193508773)
     -- 0x40df499974f62e2f268cd5096b0d952073900054122ffce0a27c9d96932891a5
    ]
    [
     (builtin bls12_381_G1_uncompress)
     (con bytestring #a077246742bfbffdefc1193aba17434d337f231478bf63173065c1e09c34429e76877983ae5f3add1438e5d237f63724)
    ]
   ]
  ]
  (con
   bls12_381_G1_element
   0xa07796202c3fcad405a5da58d99f0194c8ee21999dd03291f0bfe97e68eb4e69077cf8052b9f5d9cbc4a1394baa0e0d8
  )
 ]
)
