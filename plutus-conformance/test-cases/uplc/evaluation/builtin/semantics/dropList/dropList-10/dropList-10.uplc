-- This should return the empty list.  However, if run in restricting mode it
-- will (probably, depending on the cost model) attempt to consume the maxmimum
-- budget and fail because the cost depends on how many elements you want to
-- drop, irrespective of the size of the list.
(program 1.0.0
 [
  [ (force (builtin dropList)) (con integer -12345678901234567890) ]
    (con (list integer) [11,22,33,44,55,66,77,88,99])
  ]
)
