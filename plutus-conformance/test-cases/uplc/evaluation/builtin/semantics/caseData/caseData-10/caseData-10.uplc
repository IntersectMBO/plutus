-- Unused cases can have the wrong type.
(program 1.0.0
 [
  [
   [
    [
     [
      [
       (force (builtin caseData))
       (con bool True)
      ]
      (con unit ())
     ]
     (force (builtin tailList))
    ]
    [(builtin modInteger) (con bytestring #123fff)]
   ]
   (con bytestring #9988dd)
  ]
  (con data (List [I 33, B #1234FB, List []]))
 ]
)

  