-- The scrutinee is evaluated before any alternative is inspected.
(program 1.2.0
  (match (error)
    (pattern (wildcard) (con integer 42)))
)
