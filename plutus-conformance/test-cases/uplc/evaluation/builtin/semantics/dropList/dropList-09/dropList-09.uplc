-- This should return the empty list, but in fact it will probably run out of
-- budget because the cost depends on how many elements you want to drop,
-- irrespective of the size of the list.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer 100000000000000000) ]
    (con (list integer) [11,22,33,44,55,66,77,88,99])
  ]
)