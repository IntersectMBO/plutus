-- Dropping a negative number of elements succeeds and returns the list unchanged.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer -7) ]
    (con (list integer) [11,22,33,44,55,66,77,88,99])
  ]
)
