-- Check that trying to encode an integer to a bytestring usingn too narrow a width fails.
(program 1.0.1
  [(builtin integerToByteString) (con bool True) (con integer 5) (con integer 20016001699311)]
)
