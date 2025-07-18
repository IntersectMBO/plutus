-- case on True with 3+ branches fails
(program 1.1.0
    (case (con bool True) (con integer 0) (con integer 1) (con integer 2))
)