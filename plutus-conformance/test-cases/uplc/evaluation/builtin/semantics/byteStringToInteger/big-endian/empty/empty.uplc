-- The empty bytestring decodes to 0
(program 1.0.0
 [(builtin byteStringToInteger) (con bool True) (con bytestring #)]
)
