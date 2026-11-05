-- Nonempty indices with an empty array fail
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array integer) [])
    ]
    (con (list integer) [0])
  ]
)
