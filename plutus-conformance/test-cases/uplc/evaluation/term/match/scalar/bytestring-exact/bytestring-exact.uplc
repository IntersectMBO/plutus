-- Reject a different length and equal-length unequal contents before selecting the exact bytestring.
(program 1.2.0
  (match (con bytestring #abcd)
    (pattern (bytestring #ab) (error))
    (pattern (bytestring #abce) (error))
    (pattern (bytestring #abcd) (con integer 42))
    (pattern (wildcard) (error)))
)
