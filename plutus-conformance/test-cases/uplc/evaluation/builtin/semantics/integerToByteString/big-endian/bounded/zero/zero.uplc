-- Zero should encode to a bytestring consisting entirely of zero bytes.
(program 1.0.0
 [(builtin integerToByteString) (con bool True) (con integer 12) (con integer 0)]
)
