(program 1.2.0
  (match (con bool True)
    (pattern (bool False) (error))
    (pattern (bool True) (con integer 42)))
)
