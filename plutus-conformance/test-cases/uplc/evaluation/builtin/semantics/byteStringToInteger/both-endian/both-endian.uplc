-- Check that the big-endian decoding of a bytestring is the same as the
-- little-endian decoding of its reverse.
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin byteStringToInteger) (con bool False) (con bytestring #92828b9d9e097a23ef34ba5522ee67)]
  [(builtin byteStringToInteger) (con bool True)  (con bytestring #67ee2255ba34ef237a099e9d8b8292)]
 ]
)

