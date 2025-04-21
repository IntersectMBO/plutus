-- Second argument is applied to head and tail of list
(program 1.0.0
 [
  [
   [
    (force (force (builtin caseList)))
    (con unit ())
   ]
   (lam x
    (lam y
     [
      [
       (builtin multiplyInteger)
       x
      ]
      [(force (builtin headList)) y]
     ]
    )
   )
  ]
  (con (list integer) [11, 22, 33, 44, 55, 66, 77])
 ]
)
