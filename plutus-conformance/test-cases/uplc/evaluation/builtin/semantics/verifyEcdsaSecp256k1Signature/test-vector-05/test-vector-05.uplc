-- Generated using OpenSSL 3.0.14.4
-- Signing key a1adc24fc72eeb3ca032f68134a21c83dbebed4d7088a3794dbe65b4570604fd
-- Same keypair and message as test-vector-01, sha3_256 instead of sha2_256
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
  (con bytestring #5958fe71b4498446de57d0416ab8c41155fc16d46844fbc3fc9898bfca6badf9777d01c5b74b002678bfe904e941c096b5faf613a37b4d518e0ca750abcfa020)
 ]
)
