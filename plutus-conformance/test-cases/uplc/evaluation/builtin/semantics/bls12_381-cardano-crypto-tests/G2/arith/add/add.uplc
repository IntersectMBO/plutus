-- Check that adding two random points in G2 gives the expected result.
(program 1.0.0
 [
  [
   (builtin bls12_381_G2_equal)
   [
    [
     (builtin bls12_381_G2_add)
     [
      (builtin bls12_381_G2_uncompress)
      (con
       bytestring
       #b5ed6482bf5486831a9eb445b8b9a77aa6330005b8b432523c69fee7085d3032856de9f857c55ac9745eabcf14894205149cc67393687289e6c2728be69ad1f8ea1a6c0a5a65bf93eca984f3dac5da1abc6f7156ccbc5a33c655f7b17724eb19
      )
     ]
    ]
    [
     (builtin bls12_381_G2_uncompress)
     (con
      bytestring
      #a6cc0f01663fd65a95d1359758ebe3a412ce05f4242b0c1f5964351b38e188362a8ceb6c2f86d3f7e5f73b60cd04288005d2a50f8ddf1751d7a915515054276fbae7569c3f18c614c9954177d8e745e98404654cf759d4747b0c806bbd336b7d
     )
    ]
   ]
  ]
  (con
   bls12_381_G2_element
   0xb3db03681aaf0d218be32f7cc94bd6a975c6870b4a1d4e461b77b60eee2461ca367154b0c4583b2d5f81124aa21fdf3e09ff6b54ce7c57572283a175fba381a32ac6f46abaf11cdbaeb206dcd7d4269caa4d0ebbb3adc1b8fce42ccfa855ea83
  )
 ]
)
