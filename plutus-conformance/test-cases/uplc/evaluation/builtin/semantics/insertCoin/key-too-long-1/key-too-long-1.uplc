-- A key larger than 32-bit, which is not allowed
(program 1.0.0
  [ (builtin insertCoin)
    (con bytestring #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)
    (con bytestring #)
    (con integer 1)
    (con value [])
  ]
)
