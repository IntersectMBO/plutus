-- select second branch
(program 1.1.0
    (case (constr 1 (con integer 0)) (lam x (con integer 1)) (lam x (con integer 2)))
)
