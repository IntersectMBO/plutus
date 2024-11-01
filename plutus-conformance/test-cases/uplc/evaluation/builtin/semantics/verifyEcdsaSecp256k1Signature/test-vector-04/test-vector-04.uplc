-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, low-s version of signature in test-vector-03
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
  (con bytestring #603e6e7bf67152188204f76f6274d38c477bdbc3954cdaa44e4ef49691a517de2a1552cf3d1961c164edb433b705f1b1b00dfd0b629ecb03d5b4914606eab1eb)
 ]
)
