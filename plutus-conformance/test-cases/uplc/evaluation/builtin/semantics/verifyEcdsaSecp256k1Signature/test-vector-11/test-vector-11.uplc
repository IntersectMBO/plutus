-- Generated using OpenSSL 3.0.14.4
-- Signing key 144c76f7eaa087f00a0381d0b7d6ec59eac07d4ac21b58695c1118b10127d821
-- Same message as test-vector-01, different keypair with correct signature
-- Expect True
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #03173d3b9b964301a4919be323571e64301904209a32631ccc76b42b89d38c6274)
   ]
   [(builtin sha2_256) (con bytestring #)]
  ]
  (con bytestring #a40e8132923ca042d159f5fba7d2828a79dc212259121a3bfe63445bf3f620fe1b33215f4ca9eb5d41eb8e8304ddc0666236f381f3a88f54cd67740847e91b41)
 ]
)
