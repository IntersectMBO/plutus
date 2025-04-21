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
      (force (builtin tailList))
     ]
     (con unit ())
    ]
    [(builtin modInteger) (con bytestring #123fff)]
   ]
   (con bytestring #9988dd)
  ]
  (con data (Map [(I 55, B #33ff), (B #12d399, List [])]))
 ]
)

  