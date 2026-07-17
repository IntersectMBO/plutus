-- The final wildcard denotes the whole remaining list, so extra elements do not affect success.
(program 1.2.0
  (match (con (list integer) [1, 2, 3, 4, 5, 6])
    (pattern
      (prefix (list (wildcard) (wildcard) (bind)) (wildcard))
      (lam third third))
    (pattern (wildcard) (error)))
)
