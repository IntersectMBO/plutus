-- Dual law on empty inputs
(program 1.1.0
  [ (lam v (lam ps
    [ (builtin equalsData)
    [ (builtin valueData)
    [ (builtin unionValue)
    [ (builtin keepPolicies)
    ps
    v
  ]
    [ (builtin dropPolicies)
    ps
    v
  ]
  ]
  ]
    [ (builtin valueData)
    v
  ]
  ]
  ))
  (con value [])
  (con (list bytestring) [])
]
)
