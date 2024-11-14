-- Test vector 1 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659)
   ]
   (con bytestring #243f6a8885a308d313198a2e03707344a4093822299f31d0082efa98ec4e6c89)
  ]
  (con bytestring #6896bd60eeae296db48a229ff71dfe071bde413e6d43f917dc8dcf8c78de33418906d11ac976abccb20b091292bff4ea897efcb639ea871cfa95f6de339e4b0a)
 ]
)
