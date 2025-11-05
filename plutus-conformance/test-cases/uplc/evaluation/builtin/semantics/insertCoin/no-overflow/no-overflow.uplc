-- Inserts 2^17 - 1, which is the maximum allowed value for a token
(program 1.0.0
  [
    (builtin insertCoin)
    (con bytestring #)
    (con bytestring #)
    (con integer 170141183460469231731687303715884105727)
    (con value [(#, [(#, 1)])])
  ]
)
