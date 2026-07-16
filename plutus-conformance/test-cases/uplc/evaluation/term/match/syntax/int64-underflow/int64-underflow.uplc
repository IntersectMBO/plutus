-- Integer pattern payloads below signed Int64 are rejected.
(program 1.2.0
  (match (con integer -9223372036854775809)
    (pattern (integer -9223372036854775809) (con integer 42)))
)
