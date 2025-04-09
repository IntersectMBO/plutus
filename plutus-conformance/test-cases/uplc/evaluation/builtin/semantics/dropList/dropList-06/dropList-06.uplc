-- Dropping more elements than the length of the list succeeds and returns the
-- empty list.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 17) ]
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
