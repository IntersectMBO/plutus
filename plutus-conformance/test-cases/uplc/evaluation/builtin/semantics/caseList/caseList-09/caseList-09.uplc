-- Fails because arguments are evaluated strictly.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (error)
   ]
   (lam x (lam y y))
  ]
  (con (list integer) [11,22,33])
 ]
)
