-- Casing on pair expects exactly one branch
(program 1.1.0
  (case (con (pair integer bool) (42, False)) (lam l (lam r r)) (lam l (lam r r)))
)