-- Bounds are not checked for unused indices
(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
   ]
   (con (list integer) [340, 342, 344, 1000000])
  ]
  (con (list bool) [True, True, True])
 ]
)
