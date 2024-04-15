-- Check that a particular bytestring decodes to the expected integer.
(program 1.0.0
 [(builtin byteStringToInteger) (con bool True) (con bytestring #123456abcdef)]
)
