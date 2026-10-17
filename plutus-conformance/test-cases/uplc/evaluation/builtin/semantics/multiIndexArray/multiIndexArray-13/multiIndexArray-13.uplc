-- Index greater than array length fails
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array integer) [10, 20, 30, 40, 50])
    ]
    (con (list integer) [6])
  ]
)
