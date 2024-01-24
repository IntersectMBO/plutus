-- Check that a particular integer encodes to the expected bytestring
(program 1.0.1
 [(builtin integerToByteString) (con bool True) (con integer 0) (con integer 20016001699311)]
)
