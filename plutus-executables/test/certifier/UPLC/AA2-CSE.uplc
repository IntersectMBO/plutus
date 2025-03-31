(program
  1.1.0
  [
    [
      [
        (force (force (delay (delay (lam f-2 (lam x-3 [ f-2 x-3 ]))))))
        (builtin addInteger)
      ]
      [
        (lam
          x0-0
          [
            (lam
              x2-2
              [
                [
                  (builtin multiplyInteger)
                  [
                    [ (builtin divideInteger) (con integer 1) ]
                    (con integer 0)
                  ]
                ]
                (con integer 0)
              ]
            )
            [
              [
                (builtin lessThanEqualsInteger)
                (con integer 0)
              ]
              (con integer 0)
            ]
          ]
        )
          (con integer 1)
      ]
    ]
    [
      (lam x0-0 x0-0)
      [
        (lam
          x1-1
          [
            [
              (builtin multiplyInteger)
              (con integer 0)
            ]
            [ [ (builtin divideInteger) (con integer 1) ] (con integer 0) ]
          ]
        )
        (con integer 1)
      ]
    ]
  ]
)
