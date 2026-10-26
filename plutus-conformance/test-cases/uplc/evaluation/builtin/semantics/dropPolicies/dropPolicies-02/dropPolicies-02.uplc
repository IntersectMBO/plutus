-- Empty Value with requested policy
(program 1.1.0
  [ (builtin dropPolicies)
    (con (list bytestring) [#aa])
    (con value [])
  ]
)
