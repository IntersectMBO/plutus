-- branch with wrong arguments
(program 1.1.0
    (case (constr 0 (con integer 0)) (con integer 1) (lam x (con integer 2)))
)
