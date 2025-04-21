-- caseList must be forced twice.
(program 1.0.0
 [
  [
   [
    (force (builtin caseList))
    (con integer 12345)
   ]
   (lam x (lam y y))
  ]
  (con (list integer) [11, 22, 33, 44, 55, 66, 77])
 ]
)
