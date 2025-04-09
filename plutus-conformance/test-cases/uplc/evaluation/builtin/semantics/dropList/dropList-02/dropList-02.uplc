-- Dropping zero elements has no effect.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 0) ]
    (con (list bytestring)
      [ #123456
      , #234567
      , #345678
      , #456789
      , #56789a
      , #6789ab
      , #789abc
      , #89abcd93232479173417824fff
      , #ffeeffeeffee
     ]
    )
  ]
)
