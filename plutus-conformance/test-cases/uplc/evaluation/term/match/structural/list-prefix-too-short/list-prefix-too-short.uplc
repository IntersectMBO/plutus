-- A prefix still requires one input element per fixed leading pattern.
(program 1.2.0
  (match (con (list integer) [1, 2])
    (pattern
      (list (prefix (wildcard) (wildcard) (bind) (wildcard)))
      (lam third third))
    (pattern (wildcard) (con integer 99)))
)
