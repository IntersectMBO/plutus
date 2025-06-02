-- m = 3842610773*16548071329, e = -1 gcd a m = 1 -> compute inverse
(program 1.0.0
 [(builtin equalsInteger)
  [(builtin modInteger)
   [(builtin multiplyInteger)
    [(builtin expModInteger)
     (con integer 1654807132907)
     (con integer -1)
     (con integer 63587797161187827317)
    ]
    [(builtin expModInteger)
     (con integer 1654807132907)
     (con integer 1)
     (con integer 63587797161187827317)
    ]
   ]
   (con integer 63587797161187827317)
  ] (con integer 1)
 ]
)
