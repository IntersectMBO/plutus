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
                  f_2
                  [
                    (force
                      (force
                        (delay
                          (delay
                            (lam
                              f_2
                              [
                                (force (delay (lam s_1 [ s_1 s_1 ])))
                                (lam
                                  s_3
                                  (lam
                                    x_4
                                    [
                                      [
                                        f_2
                                        [
                                          (force (delay (lam s_1 [ s_1 s_1 ])))
                                          s_3
                                        ]
                                      ]
                                      x_4
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
                      rec_3
                      (lam
                        z_4
                        (lam
                          xs_5
                          [
                            [ (force xs_5) z_4 ]
                            (lam
                              x_6
                              (lam
                                xs'_7 [ [ rec_3 [ [ f_2 z_4 ] x_6 ] ] xs'_7 ]
                              )
                            )
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
        (lam
          acc_0
          (lam
            n_1
            [
              [ (builtin addInteger) acc_0 ]
              [
                [
                  [
                    (force
                      (delay
                        (lam
                          f_1
                          [
                            (force
                              (force
                                (delay
                                  (delay
                                    (lam
                                      f_2
                                      [
                                        (force (delay (lam s_1 [ s_1 s_1 ])))
                                        (lam
                                          s_3
                                          (lam
                                            x_4
                                            [
                                              [
                                                f_2
                                                [
                                                  (force
                                                    (delay
                                                      (lam s_1 [ s_1 s_1 ])
                                                    )
                                                  )
                                                  s_3
                                                ]
                                              ]
                                              x_4
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
                              rec_2
                              (lam
                                z_3
                                (lam
                                  n_4
                                  [
                                    [ (force n_4) z_3 ]
                                    (lam n'_5 [ [ rec_2 [ f_1 z_3 ] ] n'_5 ])
                                  ]
                                )
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
                n_1
              ]
            ]
          )
        )
      ]
      (con integer 0)
    ]
    [
      [
        (force
          [
            (force
              (force
                (force
                  (force
                    (delay
                      (delay
                        (delay
                          (delay
                            (lam
                              f_7
                              [
                                [
                                  (force
                                    (delay
                                      (lam
                                        by_1
                                        [
                                          (force
                                            (force
                                              (delay
                                                (delay
                                                  (lam
                                                    f_2
                                                    [
                                                      (force
                                                        (delay
                                                          (lam s_1 [ s_1 s_1 ])
                                                        )
                                                      )
                                                      (lam
                                                        s_3
                                                        (lam
                                                          x_4
                                                          [
                                                            [
                                                              f_2
                                                              [
                                                                (force
                                                                  (delay
                                                                    (lam
                                                                      s_1
                                                                      [
                                                                        s_1 s_1
                                                                      ]
                                                                    )
                                                                  )
                                                                )
                                                                s_3
                                                              ]
                                                            ]
                                                            x_4
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
                                            rec_8
                                            (lam
                                              h_11
                                              (delay
                                                (lam
                                                  fr_14
                                                  [
                                                    (force
                                                      [
                                                        by_1
                                                        (delay
                                                          (lam
                                                            fq_16
                                                            [
                                                              (force
                                                                [ rec_8 h_11 ]
                                                              )
                                                              [
                                                                (force h_11)
                                                                fq_16
                                                              ]
                                                            ]
                                                          )
                                                        )
                                                      ]
                                                    )
                                                    fr_14
                                                  ]
                                                )
                                              )
                                            )
                                          )
                                        ]
                                      )
                                    )
                                  )
                                  (lam
                                    k_9
                                    (delay
                                      (lam
                                        h_12
                                        [
                                          [
                                            h_12
                                            (lam
                                              x_15
                                              [
                                                (force k_9)
                                                (lam
                                                  f_0_13
                                                  (lam f_1_14 [ f_0_13 x_15 ])
                                                )
                                              ]
                                            )
                                          ]
                                          (lam
                                            x_18
                                            [
                                              (force k_9)
                                              (lam
                                                f_0_16
                                                (lam f_1_17 [ f_1_17 x_18 ])
                                              )
                                            ]
                                          )
                                        ]
                                      )
                                    )
                                  )
                                ]
                                f_7
                              ]
                            )
                          )
                        )
                      )
                    )
                  )
                )
              )
            )
            (delay
              (lam
                choose_9
                (lam
                  even_0
                  (lam
                    odd_1
                    [
                      [
                        choose_9
                        (lam
                          l_4
                          [
                            [
                              (force l_4)
                              (force (delay (delay (lam z_2 (lam f_3 z_2)))))
                            ]
                            (lam
                              head_2
                              (lam
                                tail_3
                                [
                                  [
                                    (force
                                      (delay
                                        (lam
                                          x_1
                                          (lam
                                            xs_2
                                            (delay
                                              (lam
                                                z_4
                                                (lam f_5 [ [ f_5 x_1 ] xs_2 ])
                                              )
                                            )
                                          )
                                        )
                                      )
                                    )
                                    head_2
                                  ]
                                  [ odd_1 tail_3 ]
                                ]
                              )
                            )
                          ]
                        )
                      ]
                      (lam
                        l_7
                        [
                          [
                            (force l_7)
                            (force (delay (delay (lam z_2 (lam f_3 z_2)))))
                          ]
                          (lam head_5 (lam tail_6 [ even_0 tail_6 ]))
                        ]
                      )
                    ]
                  )
                )
              )
            )
          ]
        )
        (lam arg_0_0 (lam arg_1_1 arg_0_0))
      ]
      [
        [
          (force
            (delay
              (lam
                x_1 (lam xs_2 (delay (lam z_4 (lam f_5 [ [ f_5 x_1 ] xs_2 ]))))
              )
            )
          )
          [
            (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
            (delay (lam z_1 (lam f_2 z_1)))
          ]
        ]
        [
          [
            (force
              (delay
                (lam
                  x_1
                  (lam xs_2 (delay (lam z_4 (lam f_5 [ [ f_5 x_1 ] xs_2 ]))))
                )
              )
            )
            [
              (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
              [
                (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
                (delay (lam z_1 (lam f_2 z_1)))
              ]
            ]
          ]
          [
            [
              (force
                (delay
                  (lam
                    x_1
                    (lam xs_2 (delay (lam z_4 (lam f_5 [ [ f_5 x_1 ] xs_2 ]))))
                  )
                )
              )
              [
                (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
                [
                  (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
                  [
                    (lam n_0 (delay (lam z_2 (lam f_3 [ f_3 n_0 ]))))
                    (delay (lam z_1 (lam f_2 z_1)))
                  ]
                ]
              ]
            ]
            (force (delay (delay (lam z_2 (lam f_3 z_2)))))
          ]
        ]
      ]
    ]
  ]
)
