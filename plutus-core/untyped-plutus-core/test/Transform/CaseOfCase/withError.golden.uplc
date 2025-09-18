(force
  [
    [ [ (force (builtin ifThenElse)) (con bool True) ] (delay (con unit ())) ]
    (delay (error))
  ]
)