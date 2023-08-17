-- <[a]P,Q> = <P,[a]Q>
(program 1.0.0
 [
  [
   (builtin bls12_381_finalVerify)
   [
    [
     (builtin bls12_381_millerLoop)
     [
      (builtin bls12_381_G1_uncompress)
      (con bytestring #8baa4f3fcd895033f93494b040ccd7dfb77cb759cd2e150bfff4264873174509cd22230423b70896b17c8fc3660f6b21)  -- [a]P
     ]
    ]
    [
     (builtin bls12_381_G2_uncompress)
     (con bytestring #b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352)  -- Q
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
      #840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669)  -- P
    ]
   ]
   [
    (builtin bls12_381_G2_uncompress)
    (con
     bytestring
     #a80f311db6f2fdc45404870f4c55b65a9a59a35efcfa2a7c595f3955226076bbaa33e403c0d4749495d9423b806f9dbe08cca770e08fa535daefb6dba2edb62f8b9aff6bae83bf48819bcdf98f07e79de8635e8521ddecae19b01a6777bc4684)  -- [a]Q
   ]
  ]
 ]
)
