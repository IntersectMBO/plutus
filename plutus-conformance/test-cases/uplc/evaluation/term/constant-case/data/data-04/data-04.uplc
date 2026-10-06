-- the selected handler must accept the Data.Constr fields
(program 1.2.0
  (case
    (con data (Constr 0 []))
    (con integer 42)
  )
)
