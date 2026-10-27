-- Dual law with duplicates and absent IDs
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
  (con value [(#, [(#, 1000000)]),
      (#aa, [(#01, 5), (#02, -7)]),
      (#bb, [(#, -2), (#ff, 9)]),
      (#cc, [(#01, 1)])])
  (con (list bytestring) [#bb, #, #dd, #bb, #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
]
)
