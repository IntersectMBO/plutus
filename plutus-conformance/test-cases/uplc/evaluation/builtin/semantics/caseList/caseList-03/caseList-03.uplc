-- Correct application to empty list, return types of branches need not be the same
(program 1.0.0
 [
  [
   [ (force (force (builtin caseList)))
     (con string "Empty")
   ]
   (lam x (lam xs [ [(builtin addInteger) x] [(force (builtin headList)) xs]]))
  ]
  (con (list integer) [])
 ]
)