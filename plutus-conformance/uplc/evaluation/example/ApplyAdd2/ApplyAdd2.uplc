(program
  1.0.0
  [
    [
      [
        (force (force (delay (delay (lam f (lam x [ f x ]))))))
        (builtin addInteger)
      ]
      [
        (lam
          x0
          [
            [
              (builtin multiplyInteger)
              [
                [
                  (builtin subtractInteger)
                  [
                    [ (builtin subtractInteger) (con integer 3) ]
                    (con integer 2)
                  ]
                ]
                [ [ (builtin addInteger) (con integer 2) ] (con integer 0) ]
              ]
            ]
            [
              [
                (builtin subtractInteger)
                [
                  [ (builtin multiplyInteger) (con integer 3) ] (con integer 0)
                ]
              ]
              [ [ (builtin multiplyInteger) (con integer 1) ] (con integer 1) ]
            ]
          ]
        )
        [
          [
            (builtin lessThanEqualsInteger)
            [
              [
                (builtin subtractInteger)
                [
                  [ (builtin multiplyInteger) (con integer 3) ] (con integer 3)
                ]
              ]
              [ [ (builtin subtractInteger) (con integer 2) ] (con integer 3) ]
            ]
          ]
          [
            [
              (builtin addInteger)
              [ [ (builtin addInteger) (con integer 2) ] (con integer 3) ]
            ]
            [ [ (builtin subtractInteger) (con integer 3) ] (con integer 3) ]
          ]
        ]
      ]
    ]
    [
      (lam
        x0
        [
          (lam
            x2
            [
              [
                (builtin addInteger)
                [
                  [ (builtin subtractInteger) (con integer 0) ] (con integer 3)
                ]
              ]
              [ [ (builtin subtractInteger) (con integer 2) ] (con integer 1) ]
            ]
          )
          [
            [
              (builtin subtractInteger)
              [ [ (builtin addInteger) (con integer 1) ] (con integer 1) ]
            ]
            [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
          ]
        ]
      )
      [
        (lam
          x1
          [
            [
              (builtin lessThanInteger)
              [ [ (builtin multiplyInteger) (con integer 0) ] (con integer 3) ]
            ]
            [ [ (builtin addInteger) (con integer 0) ] (con integer 1) ]
          ]
        )
        [
          [
            (builtin equalsInteger)
            [ [ (builtin multiplyInteger) (con integer 3) ] (con integer 2) ]
          ]
          [ [ (builtin subtractInteger) (con integer 2) ] (con integer 0) ]
        ]
      ]
    ]
  ]
)
