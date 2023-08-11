-- Check that the procedure for using a DST greater than 255 bytes long gives the expected result.
(program
 1.0.0
 [
  [
   (builtin bls12_381_G1_equal)
   [
    [
     (builtin bls12_381_G1_hashToGroup)
     (con bytestring #54657374696e67206c61726765206473742e)  -- msg: "Testing large dst."
    ]
    [
     (builtin sha2_256)
     [
      [
       (builtin appendByteString)
       (con bytestring #4832432d4f56455253495a452d4453542d)  -- prefix: "H2C-OVERSIZE-DST-"
      ]
      (con
       bytestring
       #62f5804020e6a8e242c736d1c97bcd8262f91b88e1d70b00d10d5e315c8c6501ead0a7e367e5d394b9fcff9c15aa0f6a05e5085fdc56bcdee3865016f1c49b20e1e609a606eccabc9b9199a42345c25e06ae70028397f8fb95576f264239da3eb49629d5efeb1f1d74a3b1ac58608d893f98058f5ab870833489f5dfec52db5f92e70db05c9704cd9d644b1ae16aaafcc173d48db17e207d91308d3045b042b7241f87b8d42ac5df97d94fdf3f29d20ca2ae22c22e9c5b84b48d6daf1f7959c7c71d0169f370ebf2838479b3731885ff0d278deb632fcb83aef0ab593dddd4f5d21dac56abe08b8cb4aaf4235b1a292b91d6e8b90e39dc953c75fc460e7dd6d2bc8a372ac4efce161f5f18f861e67e5717c86805a05cc53ff493e91de2b85d3166b353f5bbc64bae0d2a4787  -- large_dst: random bytes
      )
     ]
    ]
   ]
  ]
  [
   (builtin bls12_381_G1_uncompress)
   (con
    bytestring
    #a16b5778b5b88519b6caf05921d0d9b8b94a33d1daaa0c7fbfa66d52e801a5e798fae840bb9608aa31712e0b1b3a054a  -- output
   )
  ]
 ]
)
