-- case on empty list with two branches
(program 1.1.0
    (case (con (list integer) []) (lam x (lam xs x)) (con integer -1))
)