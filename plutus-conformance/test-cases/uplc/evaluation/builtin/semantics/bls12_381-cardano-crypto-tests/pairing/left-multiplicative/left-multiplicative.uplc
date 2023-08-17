-- <[a]P,[b]Q> = <[ab]P,Q>
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
       #8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21  -- [a]P
      )
     ]
    ]
    [
     (builtin bls12_381_G2_uncompress)
     (con
      bytestring
      #9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415  -- [b]Q
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
      #b2bb2433441c452b78f5be911aa136dd2c886a9ac329cb6c805e50d5255891fcc389b1190432f16a109c6f431f0f8023  -- [ab]P
     )
    ]
   ]
   [
    (builtin bls12_381_G2_uncompress)
    (con
     bytestring
     #b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352  -- Q
    )
   ]
  ]
 ]
)
