-- Check that a width greater than the maximum of 8192 is rejected when encoding zero.
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer 8193) (con integer 0)]
)
