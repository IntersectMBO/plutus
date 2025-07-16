-- case on empty list with one branch
(program 1.1.0
    (case (con (list integer) []) (lam x (lam xs x)))
)