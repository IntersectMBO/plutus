-- This value was obtained by hashing 0x0102030405 to G2 but has had the
-- compression bit cleared, so uncompression should fail.
(program 0.0.0
 [
  (builtin bls12_381_G2_uncompress)
  (con bytestring #a8138ebea766d4d1aa64dd3b5826244c32ea3fe9351f9c8d584203716dae151d14bb5d06e245c24877955c79287682ba082d077bbb2afdb1ad1d48d18e2f0c56b001bce207801adfa9fd451fc59d56f0433b02f921ba5a272c58c06536291d07)
 ]
)