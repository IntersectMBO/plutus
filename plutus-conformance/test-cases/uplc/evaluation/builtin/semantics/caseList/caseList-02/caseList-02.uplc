-- caseList can return arbitrary terms
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (lam x (lam y x))
   ]
   (con bytestring #654321)
  ]
  (con (list integer) [])
 ]
)
