-- Test vector 2 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #dd308afec5777e13121fa72b9cc1b7cc0139715309b086c960e18fd969774eb8)
   ]
   (con bytestring #7e2d58d8b3bcdf1abadec7829054f90dda9805aab56c77333024b9d0a508b75c)
  ]
  (con bytestring #5831aaeed7b44bb74e5eab94ba9d4294c49bcf2a60728d8b4c200f50dd313c1bab745879a5ad954a72c45a91c3a51d3c7adea98d82f8481e0e1e03674a6f3fb7)
 ]
)
