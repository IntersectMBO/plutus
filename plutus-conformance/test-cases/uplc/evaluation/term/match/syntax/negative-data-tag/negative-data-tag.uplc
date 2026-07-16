-- Data.Constr pattern tags cannot be negative.
(program 1.2.0
  (match (con data (Constr 0 []))
    (pattern (data-constr -1) (con integer 42)))
)
