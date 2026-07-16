(program 1.2.0
  (match (con integer 9)
    (pattern (integer 7) (error))
    (pattern (integer 8) (error))
    (pattern (wildcard) (con integer 42)))
)
