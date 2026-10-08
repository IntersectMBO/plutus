-- case on Data only supports Data.Constr values
(program 1.2.0
  (case
    (con data (I 42))
    (lam fields fields)
  )
)
