-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, sha3_256 instead of sha2_256, alternative signature
-- Expect True
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f)
   ]
   [(builtin sha3_256) (con bytestring #)]
  ]
  (con bytestring #d7086f9d50c7bbdd739c16da7d16bbabff5b58fc982013c9bac6df7a7200e3fe496c38ef025c3adf1cd060e0a74112580d9d2226213d7e70f0eee726c484e986)
 ]
)
