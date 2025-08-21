-- case on integer fails when given integer is bigger than number of branches given
(program 1.1.0
    (case (con integer 3) (con integer 42) (con integer 43) (con integer 44))
)