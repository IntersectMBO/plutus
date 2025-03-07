-- Application to empty list, unused non-empty case has wrong type
(program 1.0.0
 [
  [
   [ (force (force (builtin caseList)))
     (con string "Empty")
   ]
   (con bool False)
  ]
  (con (list integer) [])
 ]
)