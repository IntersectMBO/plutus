-- select the second Data.Constr branch and pass its fields to the handler
(program 1.1.0
  (case
    (con data (Constr 1 [I 42, B #abcd, List [I 7]]))
    (lam fields (con integer 0))
    (lam fields fields)
  )
)
