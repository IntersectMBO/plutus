-- Empty Data.List and Data.Map patterns match their corresponding empty containers exactly.
(program 1.2.0
  (match (con data (Constr 0 [List [], Map []]))
    (pattern
      (data-constr 0 (data-list) (data-map))
      (con integer 42))
    (pattern (wildcard) (error)))
)
