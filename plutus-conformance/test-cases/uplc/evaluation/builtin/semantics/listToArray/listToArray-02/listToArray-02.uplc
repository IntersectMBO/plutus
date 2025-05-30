-- convert a non-empty list to an array
(program 1.1.0
  [ (force (builtin listToArray)) 
    (con (list integer) [11,22,33,44,55,66,77,88,99]) 
  ]
)
