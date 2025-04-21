-- Succeeds and returns an integer.  The types of the branches need not match.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (con integer 123456)
   ]
   (con bytestring #654321)
  ]
  (con (list integer) [])
 ]
)
