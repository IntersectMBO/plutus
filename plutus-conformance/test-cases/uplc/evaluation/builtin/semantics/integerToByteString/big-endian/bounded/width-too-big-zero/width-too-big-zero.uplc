-- Check that a width greater than the maximum of 8000 is rejected when encoding zero.
(program 1.0.1
 [(builtin integerToByteString) (con bool True) (con integer 8001) (con integer 0)]
)