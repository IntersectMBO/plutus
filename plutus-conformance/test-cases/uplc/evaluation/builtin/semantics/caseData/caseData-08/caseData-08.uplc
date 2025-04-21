-- Unused cases can have the wrong type.
(program 1.0.0
 [
  [
   [
    [
     [
      [
       (force (builtin caseData))
       (lam c (lam l [(builtin serialiseData) [(force (builtin headList)) l]]))
      ]
      (con bool True)
     ]
     (con unit ())
    ]
    [(builtin modInteger) (con bytestring #123fff)]
   ]
   (con bytestring #9988dd)
  ]
  (con data (Constr 99 [I 33, B #1234FB, List []]))
 ]
)
