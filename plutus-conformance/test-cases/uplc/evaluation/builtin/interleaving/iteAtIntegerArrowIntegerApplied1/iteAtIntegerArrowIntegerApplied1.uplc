(program
  1.0.0
  [
    [
      [
        (force (builtin ifThenElse))
        [
          [ (builtin lessThanEqualsInteger) (con integer 11) ] (con integer 22)
        ]
      ]
      [ (builtin multiplyInteger) (con integer 11) ]
    ]
    [ (builtin subtractInteger) (con integer 22) ]
  ]
)
