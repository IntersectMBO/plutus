-- A rest capture is valid when the fixed prefix consumes the complete list.
(program 1.2.0
  (match (con (list integer) [1, 2, 3])
    (pattern
      (prefix (list (wildcard) (wildcard) (bind)) (bind))
      (lam third (lam rest rest)))
    (pattern (wildcard) (error)))
)
