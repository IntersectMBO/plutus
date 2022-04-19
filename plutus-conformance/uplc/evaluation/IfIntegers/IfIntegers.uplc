(program
  1.0.0
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
                    [ [ [ (force (builtin ifThenElse)) b ] x ] y ] (con unit ())
                  ]
                )
              )
            )
          )
        )
        [
          (lam
            x0
            [
              [
                (builtin equalsByteString)
                [
                  (builtin sha2_256) [ (builtin sha3_256) (con bytestring #64) ]
                ]
              ]
              x0
            ]
          )
          [
            [
              (builtin appendByteString)
              [
                (lam x1 [ (builtin sha3_256) (con bytestring #78) ])
                [ (builtin sha3_256) (con bytestring #726e) ]
              ]
            ]
            (con bytestring #6973)
          ]
        ]
      ]
      [
        (force (force (delay (delay (lam x (lam y x))))))
        [
          (lam
            x0
            [
              (lam x2 x0)
              [ (builtin sha2_256) [ (builtin sha3_256) (con bytestring #) ] ]
            ]
          )
          [
            [
              (builtin subtractInteger)
              [
                [
                  (builtin addInteger)
                  [
                    [ (builtin subtractInteger) (con integer 2) ]
                    (con integer 2)
                  ]
                ]
                [
                  [ (builtin subtractInteger) (con integer 1) ] (con integer 3)
                ]
              ]
            ]
            [
              (lam
                x1
                [
                  [ (builtin subtractInteger) (con integer 3) ] (con integer 3)
                ]
              )
              [
                [ (builtin equalsByteString) (con bytestring #6c7a) ]
                (con bytestring #6673)
              ]
            ]
          ]
        ]
      ]
    ]
    [ (force (force (delay (delay (lam x (lam y x)))))) (con integer 0) ]
  ]
)
