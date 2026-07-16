-- Match is built-in-only; UPLC Constr values continue to use Case.
(program 1.2.0
  (match (constr 0 (con integer 1))
    (pattern (wildcard) (con integer 42)))
)
