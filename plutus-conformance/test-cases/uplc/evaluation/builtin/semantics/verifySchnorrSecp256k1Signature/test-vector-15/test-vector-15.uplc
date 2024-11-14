-- Test vector 15 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (message of size 0)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #778caa53b4393ac467774d09497a87224bf9fab6f6e68b23086497324d6fd117)
   ]
   (con bytestring #)
  ]
  (con bytestring #71535db165ecd9fbbc046e5ffaea61186bb6ad436732fccc25291a55895464cf6069ce26bf03466228f19a3a62db8a649f2d560fac652827d1af0574e427ab63)
 ]
)
