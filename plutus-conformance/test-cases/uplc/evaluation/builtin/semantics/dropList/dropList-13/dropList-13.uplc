-- Dropping any number of elements from an empty list always succeeds (and
-- returns the empty list).
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 1234) ]
    (con (list (pair (list integer) unit)) [])
  ]
)
