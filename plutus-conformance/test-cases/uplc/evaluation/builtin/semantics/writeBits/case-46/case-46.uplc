-- We can apply an empty list of updates to the empty bytestring
(program 1.0.0
[ (builtin writeBits)
  (con bytestring #)
  (con (list integer) [])
  (con bool True)
 ]
)
