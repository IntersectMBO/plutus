-- List elements retain their values, order and duplicates
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array (list integer)) [[10, 20], []])
    ]
    (con (list integer) [1, 0, 1])
  ]
)
