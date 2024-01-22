-- Zero should encode to the empty bytestring.
(program 1.0.1
 [(builtin integerToByteString) (con bool False) (con integer 0) (con integer 0)]
)
