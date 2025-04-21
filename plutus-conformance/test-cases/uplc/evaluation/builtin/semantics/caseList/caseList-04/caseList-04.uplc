-- Fails because it tries to apply a bytestring to the head and tail of the list.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (con integer 123456)
   ]
   (con bytestring #654321)
  ]
  (con (list integer) [11, 22, 33])
 ]
)
