-- The final bind captures the untouched suffix after the fixed leading patterns.
(program 1.2.0
  (match (con (list integer) [1, 2, 3, 4, 5, 6])
    (pattern
      (prefix (list (wildcard) (wildcard) (bind)) (bind))
      (lam third (lam rest rest)))
    (pattern (wildcard) (error)))
)
