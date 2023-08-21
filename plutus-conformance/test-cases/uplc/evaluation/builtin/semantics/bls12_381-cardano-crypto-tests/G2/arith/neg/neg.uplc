-- Check that negating a random point in G2 gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G2_equal)
   [
    (builtin bls12_381_G2_neg)
    [
     (builtin bls12_381_G2_uncompress)
     (con bytestring #b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19
     )
    ]
   ]
  ]
  (con
    bls12_381_G2_element
    0x95ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19
  )
 ]  
)
