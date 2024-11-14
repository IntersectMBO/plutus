-- Test vector 17 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 17)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117)
   ]
   (con bytestring #0102030405060708090a0b0c0d0e0f1011)
  ]
  (con bytestring #5130f39a4059b43bc7cac09a19ece52b5d8699d1a71e3c52da9afdb6b50ac370c4a482b77bf960f8681540e25b6771ece1e5a37fd80e5a51897c5566a97ea5a5)
 ]
)
