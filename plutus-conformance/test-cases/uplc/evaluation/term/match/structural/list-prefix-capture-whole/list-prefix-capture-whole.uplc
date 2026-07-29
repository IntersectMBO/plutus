-- With no fixed leading patterns, the final bind captures the complete builtin list.
(program 1.2.0
  (match (con (list integer) [1, 2, 3])
    (pattern (list (prefix (bind))) (lam whole whole))
    (pattern (wildcard) (error)))
)
