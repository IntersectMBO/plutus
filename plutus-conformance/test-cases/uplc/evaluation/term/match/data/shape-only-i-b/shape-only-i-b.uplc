-- Data.I and Data.B without child patterns inspect only the Data constructor shape.
(program 1.2.0
  (match (con data (List [I 9223372036854775808, B #deadbeef]))
    (pattern (data-list (data-i) (data-b)) (con integer 42))
    (pattern (wildcard) (error)))
)
