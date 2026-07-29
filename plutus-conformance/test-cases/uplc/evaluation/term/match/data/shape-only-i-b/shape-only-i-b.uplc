-- Wildcard payload patterns inspect only the Data.I and Data.B constructor shapes.
(program 1.2.0
  (match (con data (List [I 9223372036854775808, B #deadbeef]))
    (pattern (data-list (data-i (wildcard)) (data-b (wildcard))) (con integer 42))
    (pattern (wildcard) (error)))
)
