-- This would add up to (-2^-127 - 1), which is under the allowed minimum value of a
-- token
(program 1.0.0
  [ (builtin unionValue)
    (con value [(#aa, [(#aa, -170141183460469231731687303715884105728)])])
    (con value [(#aa, [(#aa, -1)])])
  ]
)
