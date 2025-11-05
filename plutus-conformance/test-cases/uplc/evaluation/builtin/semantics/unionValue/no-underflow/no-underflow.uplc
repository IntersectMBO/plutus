-- This adds up to -2^-127, which is the minimum allowed value for a single
-- token
(program 1.0.0
  [ (builtin unionValue)
    (con value [(#aa, [(#aa, -170141183460469231731687303715884105727)])])
    (con value [(#aa, [(#aa, -1)])])
  ]
)
