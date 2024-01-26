-- A bytestring consisting entirely of zeros decodes to 0.
(program 1.0.0
 [(builtin byteStringToInteger) (con bool True) (con bytestring #00000000000000000000000000)]
)
