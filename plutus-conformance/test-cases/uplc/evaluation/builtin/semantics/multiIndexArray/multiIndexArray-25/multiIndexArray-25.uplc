-- Pair elements retain their values, order and duplicates
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array (pair integer bool)) [(10, False), (20, True)])
    ]
    (con (list integer) [1, 0, 1])
  ]
)
