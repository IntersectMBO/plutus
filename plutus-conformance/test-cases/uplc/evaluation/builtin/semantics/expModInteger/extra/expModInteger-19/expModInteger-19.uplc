-- m > 1, e = 1 -> return b modulo m
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin expModInteger)
   (con integer 117)
   (con integer 1)
   (con integer 1000)
  ]
  [(builtin modInteger)
   (con integer 117)
   (con integer 1000)
  ]
 ]
)
