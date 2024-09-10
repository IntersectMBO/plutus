-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
(program 1.0.0
 [
  [
   (builtin equalsByteString)
   [
    (builtin ripemd_160)
    (con bytestring #)
   ]
  ]
 (con bytestring #9c1185a5c5e9fc54612808977ee8f548b2258d31)
 ]
)
