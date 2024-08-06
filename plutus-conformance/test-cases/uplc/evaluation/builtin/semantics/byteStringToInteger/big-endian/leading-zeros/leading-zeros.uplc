-- Check that leading zeros don't affect the result of a big-endian decoding.
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin byteStringToInteger) (con bool True) (con bytestring #123456abcdef)]
  [(builtin byteStringToInteger) (con bool True) (con bytestring #0000000000000000123456abcdef)]
 ]
)
