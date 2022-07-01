(program
  1.0.0
  [
    [
      [
        (force
          (force
            (delay
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
                                      [
                                        f [ (force (delay (lam s [ s s ]))) s ]
                                      ]
                                      x
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
                        (lam
                          xs
                          [
                            [ (force xs) z ]
                            (lam x (lam xs' [ [ rec [ [ f z ] x ] ] xs' ]))
                          ]
                        )
                      )
                    )
                  ]
                )
              )
            )
          )
        )
        (builtin addInteger)
      ]
      (con integer 0)
    ]
    (force (delay (delay (lam z (lam f z)))))
  ]
)
