-- Maximum-length policy
(program 1.1.0
  [ (builtin dropPolicies)
    (con (list bytestring) [#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff])
    (con value [(#00, [(#, -170141183460469231731687303715884105728)]),
      (#0000, [(#01, 170141183460469231731687303715884105727)]),
      (#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, [(#ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, -1)])])
  ]
)
