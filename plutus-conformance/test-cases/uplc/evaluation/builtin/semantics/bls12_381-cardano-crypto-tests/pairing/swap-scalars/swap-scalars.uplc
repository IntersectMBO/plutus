-- <[a]P,[b]Q> = <[b]P,[a]Q>
(program 1.0.0
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
      #a4a925cb9c0580c14cbc8ec54447eb20070336a61c349c6a64b0d87e4db89d77734021cd88e2da369bdd85c0518c66c4  -- [b]P
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
)
