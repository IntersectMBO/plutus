-- Both signed Int64 endpoints are valid patterns, and alternatives are ordered.
(program 1.2.0
  (match (con integer 9223372036854775807)
    (pattern (integer -9223372036854775808) (error))
    (pattern (integer 9223372036854775807) (con integer 42))
    (pattern (wildcard) (error)))
)
