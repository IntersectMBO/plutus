-- Check that a particular integer encodes to the expected bytestring using exactly the right width.
(program 1.0.1
 [(builtin integerToByteString) (con bool False) (con integer 6) (con integer 20016001699311)]
)
