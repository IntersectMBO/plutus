(program
  1.0.0
  [
    [
      [
        (force
          (delay
            (lam
              f
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
                                x
                                [
                                  [ f [ (force (delay (lam s [ s s ]))) s ] ] x
                                ]
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
                    z
                    (lam n [ [ (force n) z ] (lam n' [ [ rec [ f z ] ] n' ]) ])
                  )
                )
              ]
            )
          )
        )
        [ (builtin addInteger) (con integer 1) ]
      ]
      (con integer 0)
    ]
    [ (lam n (delay (lam z (lam f [ f n ])))) (delay (lam z (lam f z))) ]
  ]
)
