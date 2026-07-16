-- Match is rejected by the textual parser before UPLC 1.2.0.
(program 1.1.0
  (match (con integer 0)
    (pattern (wildcard) (con integer 42)))
)
