-- Check that we can encode zero using the maximum width (8000).
(program 1.0.1
 [(builtin integerToByteString) (con bool False) (con integer 8000) (con integer 0)]
)