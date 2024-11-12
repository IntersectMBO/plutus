-- Test vector 16 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 1 (added 2022-12)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117)
   ]
   (con bytestring #11)
  ]
  (con bytestring #08a20a0afef64124649232e0693c583ab1b9934ae63b4c3511f3ae1134c6a303ea3173bfea6683bd101fa5aa5dbc1996fe7cacfc5a577d33ec14564cec2bacbf)
 ]
)
