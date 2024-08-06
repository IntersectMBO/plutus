-- Check that a particular integer encodes to the expected bytestring using exactly the right width.
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer 6) (con integer 20016001699311)]
)
