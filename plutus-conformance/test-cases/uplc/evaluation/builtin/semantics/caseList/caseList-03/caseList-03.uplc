-- caseList can return arbitrary terms, even ill-typed partial builtin applications.
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    [(builtin appendByteString) (con bool True)]
   ]
   (con unit ())
  ]
  (con (list integer) [])
 ]
)
