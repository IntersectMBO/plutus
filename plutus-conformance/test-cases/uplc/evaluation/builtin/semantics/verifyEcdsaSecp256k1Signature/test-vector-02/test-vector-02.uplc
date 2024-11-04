-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, alternative signature (high r, low s)
-- Expect True
(program 1.0.0
 [
  [
   [
    (builtin verifyEcdsaSecp256k1Signature)
    (con bytestring #032e433589dce61863199171f4d1e3fa946a5832621fcd29559940a0950f96fb6f)
   ]
   [(builtin sha2_256) (con bytestring #)]
  ]
  (con bytestring #ccfd8a4781b4d69121727222f062d2c77e97496e1c701d3a0abd840207e6dcd1016c0ee3d92f1eec1ca335ec3eb285612fb82ee2c1d1f80e706b2e907dc60cc4)
 ]
)
