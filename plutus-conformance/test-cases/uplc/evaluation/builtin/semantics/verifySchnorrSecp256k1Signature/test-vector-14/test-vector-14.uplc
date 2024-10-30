-- Test vector 14 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect failure (public key is not a valid X coordinate because it exceeds the field size)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc30)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e17776969e89b4c5564d00349106b8497785dd7d1d713a8ae82b32fa79d5f7fc407d39b)
 ]
)
