(program
  1.0.0
  [
    (lam
      i0
      [
        [
          (force
            (force
              (delay
                (delay
                  (lam
                    f
                    [
                      (force (delay (lam s [ s s ])))
                      (lam
                        s
                        (lam
                          x [ [ f [ (force (delay (lam s [ s s ]))) s ] ] x ]
                        )
                      )
                    ]
                  )
                )
              )
            )
          )
          (lam
            rec
            (lam
              i
              [
                [
                  [
                    (force
                      (delay
                        (lam
                          b
                          (lam
                            x
                            (lam
                              y
                              [
                                [ [ [ (force (builtin ifThenElse)) b ] x ] y ]
                                (con unit ())
                              ]
                            )
                          )
                        )
                      )
                    )
                    [ [ (builtin lessThanEqualsInteger) i ] (con integer 1) ]
                  ]
                  (lam u i)
                ]
                (lam
                  u
                  [
                    [
                      (builtin addInteger)
                      [
                        rec [ [ (builtin subtractInteger) i ] (con integer 1) ]
                      ]
                    ]
                    [ rec [ [ (builtin subtractInteger) i ] (con integer 2) ] ]
                  ]
                )
              ]
            )
          )
        ]
        i0
      ]
    )
    (con integer 0)
  ]
)
