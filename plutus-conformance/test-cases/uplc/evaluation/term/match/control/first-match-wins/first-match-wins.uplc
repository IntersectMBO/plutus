-- The later exact alternative must not supersede an earlier overlapping wildcard.
(program 1.2.0
  (match (con integer 42)
    (pattern (wildcard) (con integer 1))
    (pattern (integer 42) (error)))
)
