-- Correct application to empty list
(program 1.0.0
 [
  [
   [ (force (force (builtin caseList)))
     (con integer -111)
   ]
   (lam x (lam xs [ [(builtin addInteger) x] [(force (builtin headList)) xs]]))
  ]
  (con (list integer) [])
 ]
)