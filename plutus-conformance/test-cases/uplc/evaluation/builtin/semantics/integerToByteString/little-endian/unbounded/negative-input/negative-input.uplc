-- Negative inputs cause an error.
(program 1.0.0
 [(builtin integerToByteString) (con bool False) (con integer 0) (con integer -5)]
)
 