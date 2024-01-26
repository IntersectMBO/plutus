-- Check that trying to encode an integer to a bytestring using too narrow a width fails.
(program 1.0.0
  [(builtin integerToByteString) (con bool False) (con integer 5) (con integer 20016001699311)]
)
