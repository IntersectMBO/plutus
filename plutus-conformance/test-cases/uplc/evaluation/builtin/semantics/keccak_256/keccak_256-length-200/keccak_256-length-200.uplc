-- Test vector (200-bit input) from ShortMsgKAT_256.txt in
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
    (con bytestring #AAFDC9243D3D4A096558A360CC27C8D862F0BE73DB5E88AA55)
   ]
  ]
 (con bytestring #6FFFA070B865BE3EE766DC2DB49B6AA55C369F7DE3703ADA2612D754145C01E6)
 ]
)
