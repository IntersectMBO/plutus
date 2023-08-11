-- Test vector (0-bit input) from SHA256ShortMessage.rsp in
-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin sha2_256)
    (con bytestring #)
   ]
  ]
 (con bytestring #e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855)
 ]
)
