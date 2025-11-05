-- Inserts -2^127 - 1, which exceeds the minimum allowed value of a token
(program 1.0.0
  [
    (builtin insertCoin)
    (con bytestring #)
    (con bytestring #)
    (con integer -170141183460469231731687303715884105729)
    (con value [(#, [(#, 1)])])
  ]
)
