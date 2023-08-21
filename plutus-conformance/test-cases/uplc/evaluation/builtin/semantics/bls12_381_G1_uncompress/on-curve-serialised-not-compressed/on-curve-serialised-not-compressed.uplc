-- This checks that the uncompression function fails on a valid *serialised* G1
-- point (obtained by hashing 0x0102030405 onto G1).  The deserialisation
-- function in the blst library can handle both serialised and compressed
-- points, but we should fail on the former.
(program 0.0.0
 [ (builtin bls12_381_G1_uncompress)
  (con bytestring
  #01e9a0c68985059bd25a5ef05b351ca22f7d7c19e37928583ae12a1f4939440ff754cfd85b23df4a54f66c7089db6deb12ae8470d881eb628dfcf4bb083fb8a6968d907a0c265f6d06e04b05a19418d395d3e0c115430f88e7156822904ef5bf)
]
)