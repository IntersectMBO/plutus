-- Dropping any number of elements from an empty list always succeeds (and
-- returns the empty list).
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 0) ]
    (con (list (pair unit integer)) [])
  ]
)
