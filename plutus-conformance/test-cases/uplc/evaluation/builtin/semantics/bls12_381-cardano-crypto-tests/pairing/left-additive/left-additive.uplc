-- <[a]P,Q><[b]P,Q> = <[a+b]P,Q>
(program
 1.0.0
 [
  [
   (builtin bls12_381_finalVerify)
   [
    [
     (builtin bls12_381_mulMlResult)
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
        #b67029fbf3ab8e62ab6b499f541537fc07d9466e668392df2bc19762d7dc48b64be09a448cd46dbfe21819a91cd0ab3205f1316ad1cc32853f3f1a1d06497f5cfbc2d753dfc01bff177adeb93f24d452045435dc6eb29f5610b66cd0dd3fb352  -- Q
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
        #a4a925cb9c0580c14cbc8ec54447eb20070336a61c349c6a64b0d87e4db89d77734021cd88e2da369bdd85c0518c66c4  -- [b]P
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
  ]
  [
   [
    (builtin bls12_381_millerLoop)
    [
     (builtin bls12_381_G1_uncompress)
     (con
      bytestring
      #aecf54083187026a6b689e70af54375ab7cc6d0d311acb6203730a2904654d6e92f82e62006c0d5e21094155eb93cc98  -- [a+b]P
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
