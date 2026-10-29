(lam
  b
  (lam
    t
    (case
      [ [ [ (force (builtin ifThenElse)) b ] t ] (constr 1) ]
      (con integer 1)
      (con integer 2)
    )
  )
)