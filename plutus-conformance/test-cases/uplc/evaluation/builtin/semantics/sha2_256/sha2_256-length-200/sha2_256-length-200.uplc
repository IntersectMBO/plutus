-- Test vector (200-bit input) from SHA256ShortMessage.rsp in
-- https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip
(program 1.0.0
 [
  [ 
   (builtin equalsByteString)
   [
    (builtin sha2_256)
    (con bytestring #2e7ea84da4bc4d7cfb463e3f2c8647057afff3fbececa1d200)
   ]
  ]
 (con bytestring #76e3acbc718836f2df8ad2d0d2d76f0cfa5fea0986be918f10bcee730df441b9)
 ]
)
