(program
  1.1.0
  [
    [(builtin equalsInteger)
  	    [ (builtin lengthOfArray) (con (array integer) [1 , 2 , 3 , 4] )  ]
    ]
  	[ (builtin lengthOfArray) [ (builtin listToArray) (con (list integer) [1 , 2 , 3 , 4] ) ] ]
  ]
)
