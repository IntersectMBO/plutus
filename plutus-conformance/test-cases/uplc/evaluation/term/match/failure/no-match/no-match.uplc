-- String has no scalar pattern and there is no fallback alternative.
(program 1.2.0
  (match (con string "opaque")
    (pattern (integer 0) (con integer 0)))
)
