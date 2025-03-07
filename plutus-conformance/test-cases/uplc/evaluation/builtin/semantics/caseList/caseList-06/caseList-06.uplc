-- Application to non-empty list, attempt to apply non-function
(program 1.0.0
 [
  [
   [ (force (force (builtin caseList)))
     (con string "Empty")
   ]
   (con bool False)
  ]
  (con (list integer) [222, -555, 777])
 ]
)