-- A childless list pattern is exact: it matches the empty list.
(program 1.2.0
  (match (con (list integer) [])
    (pattern (list) (con integer 42))
    (pattern (wildcard) (error)))
)
