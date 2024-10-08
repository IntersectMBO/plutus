(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
   ]
   (con (list integer) [340, 342, 343, 1, 2, 3]) -- The leading indices are used if the lists are of different lengths.
  ]
  (con (list bool) [True, True, True])
 ]
)