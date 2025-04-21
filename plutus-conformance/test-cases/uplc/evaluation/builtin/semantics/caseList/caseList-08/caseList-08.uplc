-- Fails because arguments are evaluated strictly.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (con unit ())
   ]
   (error)
  ]
  (con (list integer) [])
 ]
)
