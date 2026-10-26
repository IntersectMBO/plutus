-- Retain negative quantities in the complement
(program 1.1.0
  [ (builtin dropPolicies)
    (con (list bytestring) [#aa])
    (con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
  ]
)
