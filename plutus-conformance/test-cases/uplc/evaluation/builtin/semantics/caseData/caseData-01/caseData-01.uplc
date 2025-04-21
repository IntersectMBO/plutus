-- Normal operation, Constr
(program 1.0.0
 [
  [
   [
    [
     [
      [
       (force (builtin caseData))
       (lam c (lam l c)) -- Constr
      ]
      (lam m m) -- Map
     ]
     (lam l l) -- List
    ]
    (lam i i) -- I
   ]
   (lam b b) -- B
  ]
  (con data (Constr 99 [I 33, B #1234FB, List []]))
 ]
)

  