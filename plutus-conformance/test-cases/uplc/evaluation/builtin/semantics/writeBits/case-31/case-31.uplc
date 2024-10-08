-- Later occurences of duplicate indices take precedence.
(program 1.0.0
 [
  [
   [
    (builtin writeBits)
    (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000000000)
   ]
   (con (list integer) [340, 342, 343, 340, 342, 343])
  ]
  (con (list bool) [True, True, True, False, False, False])
 ]
)