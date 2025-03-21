(program
  1.0.0
  [
    (lam
      i-0
      [
        (lam
          i-1
          [
            (lam
              i-2
              [
                (lam
                  i-3
                  [
                    (lam
                      i-4
                      (lam
                        i-5
                        (lam
                          i-6
                          (lam
                            i-7
                            (lam
                              i-8
                              [
                                (lam
                                  i-9
                                  [
                                    [ [ i-9 i-9 ] i-5 ]
                                    [
                                      (builtin unMapData)
                                      [
                                        i-1
                                        [
                                          i-0
                                          [
                                            i-0
                                            [
                                              i-0
                                              [
                                                i-0
                                                [
                                                  i-0
                                                  [
                                                    i-0
                                                    [
                                                      i-2
                                                      [
                                                        (builtin unConstrData)
                                                        [
                                                          i-1
                                                          [
                                                            i-2
                                                            [
                                                              (builtin
                                                                unConstrData
                                                              )
                                                              i-8
                                                            ]
                                                          ]
                                                        ]
                                                      ]
                                                    ]
                                                  ]
                                                ]
                                              ]
                                            ]
                                          ]
                                        ]
                                      ]
                                    ]
                                  ]
                                )
                                (lam
                                  i-10
                                  (lam
                                    i-11
                                    (lam
                                      i-12
                                      (force
                                        [
                                          [
                                            [
                                              i-4
                                              [
                                                [
                                                  (builtin equalsData)
                                                  [ i-3 [ i-1 i-12 ] ]
                                                ]
                                                i-11
                                              ]
                                            ]
                                            (delay (con unit ()))
                                          ]
                                          (delay
                                            [
                                              [ [ i-10 i-10 ] i-11 ]
                                              [ i-0 i-12 ]
                                            ]
                                          )
                                        ]
                                      )
                                    )
                                  )
                                )
                              ]
                            )
                          )
                        )
                      )
                    )
                    (force (builtin ifThenElse))
                  ]
                )
                (force (force (builtin fstPair)))
              ]
            )
            (force (force (builtin sndPair)))
          ]
        )
        (force (builtin headList))
      ]
    )
    (force (builtin tailList))
  ]
)
