-- Check that a particular bytestring decodes to the expected integer.
(program 1.0.1
 [(builtin equalsInteger)
  [(builtin byteStringToInteger) (con bool True) (con bytestring #123456abcdef)]
  (con integer 20016001699311)
 ]
)
