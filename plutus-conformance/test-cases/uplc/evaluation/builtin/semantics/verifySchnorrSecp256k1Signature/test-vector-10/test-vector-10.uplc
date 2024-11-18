-- Test vector 10 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect False
-- (sG - eP is infinite. Test fails in single verification if has_even_y(inf) is defined as true and x(inf) as 1)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #00000000000000000000000000000000000000000000000000000000000000017615fbaf5ae28864013c099742deadb4dba87f11ac6754f93780d5a1837cf197)
 ]
)
