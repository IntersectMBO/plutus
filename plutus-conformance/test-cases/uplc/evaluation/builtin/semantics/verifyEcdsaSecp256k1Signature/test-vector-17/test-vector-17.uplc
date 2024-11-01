-- r value out of range (equal to group order): one less -> False, not error
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
  (con bytestring #fffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd03641413a2f3e7b5f509294a4c2e22feb697a16b792fabfebe9d0f38403b1c929836b5a)
 ]
)
