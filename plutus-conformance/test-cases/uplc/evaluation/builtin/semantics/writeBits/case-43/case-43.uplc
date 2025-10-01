-- An empty list of updates doesn't change anything.
(program 1.0.0
[ (builtin writeBits)
  (con bytestring #FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF)
  (con (list integer) [])
  (con bool False)
 ]
)
