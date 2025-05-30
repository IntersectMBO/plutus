-- Taking an array element by index which is out of bounds 
(program 1.1.0 
  [ 
    [ 
      (force (builtin indexArray)) 
      (con (array integer) [1, 2, 3, 4, 5]) 
    ]
    (con integer 5)
  ]
)
