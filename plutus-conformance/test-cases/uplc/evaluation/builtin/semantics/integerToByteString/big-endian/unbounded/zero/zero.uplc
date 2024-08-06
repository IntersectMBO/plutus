-- Zero should encode to the empty bytestring.
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer 0) (con integer 0)]
)
