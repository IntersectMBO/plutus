-- This is OK because the branches are terms and there's no requirement that
--their types match in UPLC even if they do happen to be builtin constants.
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
      (con string "11 <= 22")
    ]
    (con integer -1111)
  ]
)
