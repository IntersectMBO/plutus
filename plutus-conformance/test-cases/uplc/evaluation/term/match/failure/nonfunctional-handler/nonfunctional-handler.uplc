-- A capture is implicitly applied to its selected handler, so a constant handler is invalid.
(program 1.2.0
  (match (con integer 1)
    (pattern (bind) (con integer 0)))
)
