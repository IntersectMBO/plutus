-- Casing on pair expects branch to take two arguments
(program 1.1.0
  (case (con (pair integer bool) (42, False)) (lam l l))
)