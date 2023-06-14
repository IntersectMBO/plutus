-- This value was obtained by hashing 0x0102030405 to G1 but has had the
-- compression bit cleared, so uncompression should fail.
(program 0.0.0
 [
  (builtin bls12_381_G1_uncompress)
  (con bytestring #81e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb)
 ]
)