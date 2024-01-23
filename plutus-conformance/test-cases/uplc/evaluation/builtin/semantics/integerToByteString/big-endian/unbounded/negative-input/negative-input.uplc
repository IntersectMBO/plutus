-- Negative inputs give an error
(program 1.0.1
 [(builtin integerToByteString) (con bool True) (con integer 0) (con integer -5)]
)
 