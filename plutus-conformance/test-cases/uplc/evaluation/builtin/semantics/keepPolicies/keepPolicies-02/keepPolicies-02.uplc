-- Empty Value with requested policy
(program 1.1.0
  [ (builtin keepPolicies)
    (con (list bytestring) [#aa])
    (con value [])
  ]
)
