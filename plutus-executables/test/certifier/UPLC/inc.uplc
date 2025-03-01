(program
  1.1.0
  [
    (lam inc-0 (force inc-0))
    (delay
      (lam
        x-1
        [
          (lam
            x-2
            [
              [
                [
                  (force
                    [ (lam `+`-3 (force `+`-3)) (delay (delay (lam v-4 v-4))) ]
                  )
                  [
                    (lam
                      addInteger-5
                      [
                        (lam
                          addInteger-6
                          [
                            (lam
                              `$fAdditiveSemigroupInteger`-7
                              (force `$fAdditiveSemigroupInteger`-7)
                            )
                            (delay (force addInteger-6))
                          ]
                        )
                        (delay
                          (lam
                            x-8
                            [
                              (lam
                                x-9
                                (lam
                                  y-10
                                  [
                                    (lam y-11 [ [ addInteger-5 x-9 ] y-11 ])
                                    y-10
                                  ]
                                )
                              )
                              x-8
                            ]
                          )
                        )
                      ]
                    )
                    (builtin addInteger)
                  ]
                ]
                (con integer 1)
              ]
              x-2
            ]
          )
          x-1
        ]
      )
    )
  ]
)