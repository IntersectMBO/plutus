-- Test vector (200-bit input) from SHA3_256ShortMessage.rsp in
-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin sha3_256)
    (con bytestring #9b3fdf8d448680840d6284f2997d3af55ffd85f6f4b33d7f8d)
   ]
  ]
 (con bytestring #25005d10e84ff97c74a589013be42fb37f68db64bdfc7626efc0dd628077493a)
 ]
)
