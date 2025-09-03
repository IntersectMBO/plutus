-- case on non-empty list with one incorrectly typed branch
(program 1.1.0
    (case (con (list integer) [1, 2, 3, 4]) (con integer -1))
)