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
     [(builtin divideInteger) (con bytestring #05)]
    ]
    [(builtin modInteger) (con integer 7264268364234183810231111)]
   ]
   (con bytestring #9988dd)
  ]
  (con data (I 100000))
 ]
)
