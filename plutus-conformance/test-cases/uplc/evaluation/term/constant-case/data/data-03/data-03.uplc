-- Data.Constr tag is out of bounds
(program 1.1.0
  (case
    (con data (Constr 2 []))
    (lam fields fields)
    (lam fields fields)
  )
)
