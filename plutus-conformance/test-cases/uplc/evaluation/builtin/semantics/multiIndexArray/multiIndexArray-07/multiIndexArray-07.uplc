-- Mixed ordering and duplicates
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array integer) [10, 20, 30, 40, 50])
    ]
    (con (list integer) [4, 0, 0, 2, 1])
  ]
)
