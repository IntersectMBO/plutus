-- <[a]P,[b]Q> = <P,[ab]Q>
(program
 1.0.0
 [
  [
   (builtin bls12_381_finalVerify)
   [
    [
     (builtin bls12_381_millerLoop)
     [
      (builtin bls12_381_G1_uncompress)
      (con
       bytestring
       #8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21 -- [a]P
      )
     ]
    ]
    [
     (builtin bls12_381_G2_uncompress)
     (con
      bytestring
      #9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415 -- [b]Q
     )
    ]
   ]
  ]
  [
   [
    (builtin bls12_381_millerLoop)
    [
     (builtin bls12_381_G1_uncompress)
     (con
      bytestring
      #840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669  -- P
     )
    ]
   ]
   [
    (builtin bls12_381_G2_uncompress)
    (con
     bytestring
     #82606f4c771ca685bfc1bb9c51c886d0daa0f63fbb0f6a24b512a1b9b92d401e556cbffdc204c0a85192c865ed73f8090da58ecd1690d5a3b236cc5d40a98988f9602a6d114edb59954ef4e21692f2d48219aeacb964604849336059ceece69f  -- [ab]Q
    )
   ]
  ]
 ]
)
