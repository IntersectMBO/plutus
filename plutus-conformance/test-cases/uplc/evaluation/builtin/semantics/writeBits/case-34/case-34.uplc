(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
   ]
   (con (list integer) [340, 342, 344, 340, 342, 343])  -- 344 is out of bounds
  ]
  (con (list bool) [True, True, True, False, False, False])
 ]
)