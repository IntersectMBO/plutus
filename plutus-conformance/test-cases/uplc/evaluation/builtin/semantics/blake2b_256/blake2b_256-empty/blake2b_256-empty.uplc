-- Test vector (0-bit input) for Blake2b_256.
-- Output obtained using the b2sum program from https://github.com/BLAKE2/BLAKE2
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin blake2b_256)
    (con bytestring #)
   ]
  ]
 (con bytestring #0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8)
 ]
)
