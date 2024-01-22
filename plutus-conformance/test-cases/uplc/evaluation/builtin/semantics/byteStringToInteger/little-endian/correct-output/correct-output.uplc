-- Check that a particular bytestring decodes to the expected integer.
(program 1.0.1
 [(builtin equalsInteger)
  [(builtin byteStringToInteger) (con bool False) (con bytestring #123456abcdef)]
  (con integer 263675211822098)
 ]
)
