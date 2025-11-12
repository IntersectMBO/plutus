-- A key larger than 32-bit, which is only allowed when inserting 0 value
(program 1.0.0
  [ (builtin insertCoin)
    (con bytestring #)
    (con bytestring #aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa)
    (con integer 0)
    (con value [(#, [(#, 1)])])
  ]
)
