-- case on non-empty list with two incorrectly typed branch
(program 1.1.0
    (case (con (list integer) [1, 2, 3, 4]) (con integer -1) (con integer -1))
)