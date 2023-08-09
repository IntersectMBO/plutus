-- <P,[a]Q><P,[b]Q> = <P,[a+b]Q>
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
         #840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669  -- P
        )
       ]
      ]
      [
      (builtin bls12_381_G2_uncompress)
      (con
       bytestring
       #a80f311db6f2fdc45404870f4c55b65a9a59a35efcfa2a7c595f3955226076bbaa33e403c0d4749495d9423b806f9dbe08cca770e08fa535daefb6dba2edb62f8b9aff6bae83bf48819bcdf98f07e79de8635e8521ddecae19b01a6777bc4684  -- [a]Q
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
       #9906a15ff959b496f478dd17348b32c033236db5a7437768a30c5ce87d9b6adfa7bf2223a0721c93a92f33abac9b2faf00d25e48b0f3cc52595264ef9ad0aa7b81e20b3c8634d577883ff5fc2373a021a1e57826f420a74f3ce0fbd2dcf79415  -- [b]Q
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
      #840463aa2f2cda89985b1f3f5eb43b9c29809765d2747d60734b19d6f90610effdfc500af7d458a3e78cee0945ddc669  -- P
     )
    ]
   ]
   [
    (builtin bls12_381_G2_uncompress)
    (con
     bytestring
     #a63be4a1a776cadc7fc2e2d823bcc905f8f9cb0ebe662360d28d9964b022a99ce34a48b2e93cfceebc9bc1d79a3338da03a41393717239e66d4db06a87510b99fe04b0840c87c4051030b25e56ba34248d9ed30c82e8e501a616097299eefd62  -- [a+b]Q
    )
   ]
  ]
 ]
)
