-- Test vector (0-bit input) for Ripemd_160.
-- Output obtained using the online tool https://emn178.github.io/online-tools/ripemd_160.html
(program 1.0.0
 [
  [
   (builtin equalsByteString)
   [
    (builtin ripemd_160)
    (con bytestring #2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200)
   ]
  ]
 (con bytestring #f18921115370b049e99dfdd49fc92b371dd7c7e9)
 ]
)
