-- Second argument is applied to head and tail of list
-- Ill-typed partial builtin application is OK.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (con unit ())
   ]
   (builtin xorByteString)
  ]
  (con (list integer) [11, 22, 33, 44, 55, 66, 77])
 ]
)
