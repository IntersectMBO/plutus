-- select second branch and do computation with the args
(program 1.1.0
    (case (constr 1 (con integer 3) (con integer 2)) (lam x (lam y [(builtin addInteger) x y])) (lam x (lam y [(builtin subtractInteger) x y])))
)
