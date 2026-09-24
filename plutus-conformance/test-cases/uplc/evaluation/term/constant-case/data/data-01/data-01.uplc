-- case on Data.Constr with no fields
(program 1.2.0
  (case
    (con data (Constr 0 []))
    (lam fields (con integer 42))
  )
)
