-- A key larger than 32-bit, which is only allowed when inserting 0 value
(program 1.0.0
  [ (builtin insertCoin)
    (con bytestring #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)
    (con bytestring #)
    (con integer 0)
    (con value [(#, [(#, 1)])])
  ]
)
