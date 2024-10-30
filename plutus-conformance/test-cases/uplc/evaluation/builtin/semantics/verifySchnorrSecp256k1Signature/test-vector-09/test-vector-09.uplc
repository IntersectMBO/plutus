-- Test vector 9 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 0)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #0000000000000000000000000000000000000000000000000000000000000000123dda8328af9c23a94c1feecfd123ba4fb73476f0d594dcb65c6425bd186051)
 ]
)
