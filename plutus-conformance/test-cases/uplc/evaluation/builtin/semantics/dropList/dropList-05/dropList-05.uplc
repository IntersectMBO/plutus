-- Dropping more elements than the length of the list succeeds and returns the
-- empty list.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 17) ]
    (con (list integer) [11,22,33,44,55,66,77,88,99])
  ]
)
