-- Test vector (0-bit input) from ShortMsgKAT_256.txt in
-- https://keccak.team/obsolete/KeccakKAT-3.zip.  The Keccak function we're
-- testing here is the version used by Ethereum, which was the Keccak submission
-- in round 3 of the SHA-3 competition.  The final SHA-3 hash function is a
-- modified version of that.
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin keccak_256)
    (con bytestring #)
   ]
  ]
 (con bytestring #C5D2460186F7233C927E7DB2DCC703C0E500B653CA82273B7BFAD8045D85A470)
 ]
)
