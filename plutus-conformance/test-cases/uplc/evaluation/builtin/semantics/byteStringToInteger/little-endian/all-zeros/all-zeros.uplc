-- A bytestring consisting entirely of zeros decodes to 0.
(program 1.0.0
 [(builtin byteStringToInteger) (con bool False) (con bytestring #00000000000000000000000000)]
)
