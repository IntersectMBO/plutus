-- Test vector 6 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False (has_even_y(R) is false)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #fff97bd5755eeea420453a14355235d382f6472f8568a18b2f057a14602975563cc27944640ac607cd107ae10923d9ef7a73c643e166be5ebeafa34b1ac553e2)
 ]
)
