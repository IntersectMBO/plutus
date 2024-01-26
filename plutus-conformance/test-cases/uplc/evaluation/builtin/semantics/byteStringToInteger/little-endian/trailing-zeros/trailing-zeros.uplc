-- Check that trailing zeros don't affect the result of a little-endian decoding.
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin byteStringToInteger) (con bool False) (con bytestring #123456abcdef)]
  [(builtin byteStringToInteger) (con bool False) (con bytestring #123456abcdef0000000000000000)]
 ]
)
