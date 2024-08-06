-- Negative widths give an error
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer -20) (con integer 5)]
)
