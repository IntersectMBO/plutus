-- An empty list of updates doesn't change anything.
(program 1.0.0
[ (builtin writeBits)
  (con bytestring #00000000000000000000000000000000000000000000000000000000000000000000000000000000)
  (con (list integer) [])
  (con bool True)
 ]
)
