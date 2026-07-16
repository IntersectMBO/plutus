-- Integer pattern payloads are restricted to signed Int64.
(program 1.2.0
  (match (con integer 9223372036854775808)
    (pattern (integer 9223372036854775808) (con integer 42)))
)
