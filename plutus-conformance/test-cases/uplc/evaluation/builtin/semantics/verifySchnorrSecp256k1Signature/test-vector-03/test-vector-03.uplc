-- Test vector 3 from https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv
-- Expect True (test fails if msg is reduced modulo p or n)
(program 1.0.0
 [
  [
   [(builtin verifySchnorrSecp256k1Signature)
    (con bytestring #25d1dff95105f5253c4022f628a996ad3a0d95fbf21d468a1b33f8c160d8f517)
   ]
   (con bytestring #ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
  ]
  (con bytestring #7eb0509757e246f19449885651611cb965ecc1a187dd51b64fda1edc9637d5ec97582b9cb13db3933705b32ba982af5af25fd78881ebb32771fc5922efc66ea3)
 ]
)
