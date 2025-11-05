-- Attempting to write to a negative position in the empty bytestring causes an error
(program 1.0.0
[ (builtin writeBits)
  (con bytestring #)
  (con (list integer) [-1])
  (con bool False)
 ]
)
