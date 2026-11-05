-- Bytestring elements retain their values, order and duplicates
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array bytestring) [#00, #ff01])
    ]
    (con (list integer) [1, 0, 1])
  ]
)
