-- case on empty list with two branches
(program 1.1.0
    (case (con (list integer) []) (con integer -1) (lam x (lam xs x)))
)