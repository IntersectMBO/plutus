-- The empty bytestring decodes to 0
(program 1.0.0
 [(builtin byteStringToInteger) (con bool False) (con bytestring #)]
)
