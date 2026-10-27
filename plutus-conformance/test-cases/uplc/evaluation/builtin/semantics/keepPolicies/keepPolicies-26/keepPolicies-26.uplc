-- Retain a policy containing negative quantities
(program 1.1.0
  [ (builtin keepPolicies)
    (con (list bytestring) [#bb])
    (con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
  ]
)
