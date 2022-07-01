(program
  1.0.0
  [
    [
      (force (force (delay (delay (lam f (lam x [ f x ]))))))
      [
        (builtin addInteger)
        [
          (lam
            x0
            [
              [
                (builtin multiplyInteger)
                [ [ (builtin multiplyInteger) x0 ] x0 ]
              ]
              [
                [
                  (builtin subtractInteger)
                  [
                    [ (builtin subtractInteger) (con integer 0) ]
                    (con integer 1)
                  ]
                ]
                [
                  [ (builtin subtractInteger) (con integer 3) ] (con integer 0)
                ]
              ]
            ]
          )
          [
            (lam
              x1
              [
                [
                  (builtin subtractInteger)
                  [
                    [ (builtin multiplyInteger) (con integer 0) ]
                    (con integer 2)
                  ]
                ]
                [ [ (builtin addInteger) (con integer 0) ] (con integer 1) ]
              ]
            )
            [
              (lam
                x2
                [
                  [ (builtin subtractInteger) (con integer 2) ] (con integer 2)
                ]
              )
              [ (builtin sha3_256) (con bytestring #76) ]
            ]
          ]
        ]
      ]
    ]
    [
      (lam
        x0
        [
          [
            (builtin addInteger)
            [
              [
                (builtin addInteger)
                [
                  [ (builtin multiplyInteger) (con integer 2) ] (con integer 1)
                ]
              ]
              [ [ (builtin addInteger) (con integer 2) ] (con integer 3) ]
            ]
          ]
          [
            [
              (builtin subtractInteger)
              [ [ (builtin subtractInteger) (con integer 1) ] (con integer 2) ]
            ]
            [ [ (builtin subtractInteger) (con integer 2) ] (con integer 1) ]
          ]
        ]
      )
      [
        [ (builtin lessThanInteger) (con integer 3) ]
        [
          [
            (builtin multiplyInteger)
            [ [ (builtin addInteger) (con integer 2) ] (con integer 1) ]
          ]
          [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
        ]
      ]
    ]
  ]
)
