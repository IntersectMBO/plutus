-- Test vector 0 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9)
   ]
   (con bytestring #0000000000000000000000000000000000000000000000000000000000000000)
  ]
  (con bytestring #e907831f80848d1069a5371b402410364bdf1c5f8307b0084c55f1ce2dca821525f66a4a85ea8b71e482a74f382d2ce5ebeee8fdb2172f477df4900d310536c0)
 ]
)
