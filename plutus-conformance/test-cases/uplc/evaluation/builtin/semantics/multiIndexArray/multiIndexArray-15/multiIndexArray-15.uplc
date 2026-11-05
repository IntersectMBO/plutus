-- Negative index beyond the machine integer range fails
(program 1.1.0
  [
    [ (force (builtin multiIndexArray))
      (con (array integer) [10, 20, 30, 40, 50])
    ]
    (con (list integer) [-18446744073709551616])
  ]
)
