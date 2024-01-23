-- Negative lengths give an error
(program 1.0.1
 [(builtin integerToByteString) (con bool True) (con integer -20) (con integer 5)]
)
 