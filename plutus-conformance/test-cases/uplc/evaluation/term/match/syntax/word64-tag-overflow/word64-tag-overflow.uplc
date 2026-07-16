-- Data.Constr pattern tags are restricted to unsigned Word64.
(program 1.2.0
  (match (con data (Constr 0 []))
    (pattern (data-constr 18446744073709551616) (con integer 42)))
)
