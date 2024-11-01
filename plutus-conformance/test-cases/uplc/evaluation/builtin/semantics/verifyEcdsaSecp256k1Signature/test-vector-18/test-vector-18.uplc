-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, but with the s component of the signature adjusted to
-- be out of range (equal to the group order): one less -> False, not error
-- Expect error
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f)
   ]
   [(builtin sha2_256) (con bytestring #)]
  ]
  (con bytestring #4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c6fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141)
 ]
)
