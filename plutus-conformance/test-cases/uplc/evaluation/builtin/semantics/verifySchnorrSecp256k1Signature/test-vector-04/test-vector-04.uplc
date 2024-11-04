-- Test vector 4 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #d69c3509bb99e412e68b0fe8544e72837dfa30746d8be2aa65975f29d22dc7b9)
   ]
   (con bytestring #4df3c3f68fcc83b27e9d42c90431a72499f17875c81a599b566c9889b9696703)
  ]
  (con bytestring #00000000000000000000003b78ce563f89a0ed9414f5aa28ad0d96d6795f9c6376afb1548af603b3eb45c9f8207dee1060cb71c04e80f593060b07d28308d7f4)
 ]
)
