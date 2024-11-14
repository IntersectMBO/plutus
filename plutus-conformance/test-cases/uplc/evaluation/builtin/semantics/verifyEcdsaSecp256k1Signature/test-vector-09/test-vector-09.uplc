-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair as test-vector-01, different message with alternative correct signature
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
  (con bytestring #fc73d27f308bb0d770db88794e2694cfe5db464764aaa8bcbcafc7c3cadb9e57244f01f2a056cf5345396e8c238972d536e4c67baa7387925d7e028f2192f5d9)
 ]
)
