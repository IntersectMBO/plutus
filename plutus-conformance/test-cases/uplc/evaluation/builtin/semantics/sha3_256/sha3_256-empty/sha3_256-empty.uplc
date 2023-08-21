-- Test vector (0-bit input) from SHA3_256ShortMessage.rsp in
-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin sha3_256)
    (con bytestring #)
   ]
  ]
 (con bytestring #a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a)
 ]
)
