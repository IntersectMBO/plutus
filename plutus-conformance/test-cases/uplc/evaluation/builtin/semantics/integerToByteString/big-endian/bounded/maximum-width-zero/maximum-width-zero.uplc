-- Check that we can encode zero using the maximum width (8192).
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer 8192) (con integer 0)]
)
