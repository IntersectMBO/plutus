(lam
  b
  (lam
    x
    (lam
      xs
      (lam
        f
        (force
          [
            [ [ (force (builtin ifThenElse)) b ] (delay [ [ f x ] xs ]) ]
            (delay (con integer 2))
          ]
        )
      )
    )
  )
)