-- Generated using OpenSSL 3.0.14.4
-- Signing key 144c76f7eaa087f00a0381d0b7d6ec59eac07d4ac21b58695c1118b10127d821
-- Same message and signature as test-vector-01, different signing key
-- Expect False
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #03173d3b9b964301a4919be323571e64301904209a32631ccc76b42b89d38c6274)
   ]
   [(builtin sha2_256) (con bytestring #)]
  ]
  (con bytestring #4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a)
 ]
)
