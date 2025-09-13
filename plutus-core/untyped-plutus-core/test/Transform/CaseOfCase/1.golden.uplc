(force
  [
    [ [ (force (builtin ifThenElse)) b ] (delay (con integer 1)) ]
    (delay (con integer 2))
  ]
)