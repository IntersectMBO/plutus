-- case on empty list with two incorrectly typed branch
(program 1.1.0
    (case (con (list integer) [1, 2, 3, 4]) (con integer -1) (lam x (lam xs x)))
)