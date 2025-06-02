-- m > 1, e = -1, gcd a m = 1 -> compute inverse
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin modInteger)
   [(builtin multiplyInteger)
    [(builtin expModInteger)
     (con integer 18)
     (con integer -1)
     (con integer 17)
    ]
    [(builtin expModInteger)
     (con integer 18)
     (con integer 1)
     (con integer 17)
    ]
   ]
   (con integer 17)
  ] (con integer 1)
 ]
)
