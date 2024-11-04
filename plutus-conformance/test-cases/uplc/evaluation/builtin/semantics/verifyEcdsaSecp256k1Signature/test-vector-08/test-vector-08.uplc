-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair as test-vector-01, different message with correct signature
-- Expect True
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f)
   ]
   [(builtin sha2_256) (con bytestring #48656c6c6f210a)]
  ]
  (con bytestring #3499b841ac6eeb300b0dc9ed50e9c196d2b74f1745540f120bf603c48189b0ee6c48eacc04f2c3d3095fa17e11cc3b7642331963d52a9177d0d0685c4b3ff17f)
 ]
)
