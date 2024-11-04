-- Test vector 8 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (negated s value)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #6cff5c3ba86c69ea4b7376f31a9bcb4f74c1976089b2d9963da2e5543e177769961764b3aa9b2ffcb6ef947b6887a226e8d7c93e00c5ed0c1834ff0d0c2e6da6)
 ]
)
