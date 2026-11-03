-- Single matching asset
(program 1.1.0
  [ (builtin keepPolicies)
    (con (list bytestring) [#aa])
    (con value [(#aa, [(#01, 42)])])
  ]
)
