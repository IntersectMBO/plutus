-- Performs 2 * 2^126 = 2^127 which exceeds the maximum allowed value (2^127 - 1)
(program 1.0.0
  [ (builtin scaleValue)
    (con integer 2)
    (con value [(#aa, [(#aa, 85070591730234615865843651857942052864)])])
  ]
)
