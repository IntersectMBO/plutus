(program
  1.0.0
  [
    [ (force (force (delay (delay (lam x (lam y x)))))) (con integer 0) ]
    [
      [
        (builtin divideInteger)
        [
          (lam
            x0
            [
              (lam x2 x2)
              [
                [
                  (builtin multiplyInteger)
                  [
                    [ (builtin multiplyInteger) (con integer 2) ]
                    (con integer 0)
                  ]
                ]
                [
                  [ (builtin subtractInteger) (con integer 1) ] (con integer 1)
                ]
              ]
            ]
          )
          [
            (lam x1 (con integer 1))
            [
              [
                (builtin subtractInteger)
                [
                  [ (builtin multiplyInteger) (con integer 2) ] (con integer 3)
                ]
              ]
              [ [ (builtin multiplyInteger) (con integer 2) ] (con integer 2) ]
            ]
          ]
        ]
      ]
      (con integer 0)
    ]
  ]
)
