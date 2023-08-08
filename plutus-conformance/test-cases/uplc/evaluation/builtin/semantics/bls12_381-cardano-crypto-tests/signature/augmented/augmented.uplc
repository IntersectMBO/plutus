-- Check that a signature involving an agumentation string prepended to a message
-- is as expected.
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
       #83422fd1d8f134fbbc7ad2949a0b7c38dc1f85bfd398bc58ae824ad34ace68eaa49f438872ee22e90778513a91f9685e  -- sig
      )
     ]
    ]
    [
     (builtin bls12_381_G2_uncompress)
     (con
      bytestring
      #93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8  -- G2 generator
     )
    ]
   ]
  ]
  [
   [
    (builtin bls12_381_millerLoop)
    [
     [
      (builtin bls12_381_G1_hashToGroup)
      [
       [
        (builtin appendByteString)
        (con
         bytestring
         #52616e646f6d2076616c756520666f722074657374206175672e20  -- aug: "Random value for test aug. "
        )
       ]
       (con bytestring #626c73742069732073756368206120626c617374)  -- msg: "blst is such a blast"

      ]
     ]
     (con
      bytestring
      #424c535f5349475f424c53313233383147325f584d443a5348412d3235365f535357555f524f5f4e554c5f
      --  DST: "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_NUL_"
     )
    ]
   ]
   [
    (builtin bls12_381_G2_uncompress)
    (con
     bytestring
     #b756d6223a92609cccf660b6f37e6e34fbb23972fc3955710f9bb202cc84cffacd337792700ebcb4324a99c7e7c9ed6d0e1cfdce8cd879a35300957c69c524c5365f6f0a85130735f27510618bbea605a1d024bb2d3bee2a5d68a827406f11c7  -- pk
    )
   ]
  ]
 ]
)
