(program
  1.0.0
  [
    [
      (builtin remainderInteger)
      [
        (lam
          x0
          [
            [
              (builtin addInteger)
              [
                (lam
                  x1
                  [ [ (builtin addInteger) (con integer 3) ] (con integer 3) ]
                )
                [
                  [ (builtin lessThanInteger) (con integer 1) ] (con integer 0)
                ]
              ]
            ]
            [
              (lam
                x2
                [
                  [ (builtin subtractInteger) (con integer 1) ] (con integer 3)
                ]
              )
              [
                [ (builtin equalsByteString) (con bytestring #7063) ]
                (con bytestring #716466)
              ]
            ]
          ]
        )
        [
          (builtin sha2_256)
          [
            [
              (builtin appendByteString)
              [ (builtin sha2_256) (con bytestring #67696d) ]
            ]
            [ (builtin sha2_256) (con bytestring #767174) ]
          ]
        ]
      ]
    ]
    (con integer 0)
  ]
)
