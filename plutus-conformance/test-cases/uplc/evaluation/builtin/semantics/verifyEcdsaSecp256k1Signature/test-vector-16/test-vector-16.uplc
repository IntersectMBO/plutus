-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same as test-vector-01, but verification key adjusted to be off the curve.
-- Expect error
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb61)
   ]
   [(builtin sha2_256) (con bytestring #)]
  ]
  (con bytestring #4941155e2303988a1be97a021fbaf9fe6064d05ea694bc5e89328f297154e5c63a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a)
 ]
)
