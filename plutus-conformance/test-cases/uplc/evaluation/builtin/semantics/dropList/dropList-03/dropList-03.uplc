-- A typical case where you really drop some elements.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 7) ]
    (con (list integer) [11,22,33,44,55,66,77,88,99])
  ]
)
