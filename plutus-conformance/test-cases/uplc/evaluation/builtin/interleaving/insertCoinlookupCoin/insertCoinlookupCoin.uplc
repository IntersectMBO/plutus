(program 1.0.0
  [ (builtin lookupCoin)
    (con bytestring #aa)
    (con bytestring #bb)
    [ (builtin insertCoin)
      (con bytestring #aa)
      (con bytestring #bb)
      (con integer 123)
      (con value [(#aa, [(#bb, 20)])])
    ]
  ]
)
