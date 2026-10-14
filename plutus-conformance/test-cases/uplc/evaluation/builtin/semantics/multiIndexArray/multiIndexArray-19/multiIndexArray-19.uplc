-- Boolean elements retain their values, order and duplicates
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array bool) [False, True])
    ]
    (con (list integer) [1, 0, 1])
  ]
)
