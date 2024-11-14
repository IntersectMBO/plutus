-- chooseUnit should accept arbitrary terms for the second argument
(program 0.0.0 [[(force (builtin chooseUnit)) (con unit ())] (lam x x)])