(program
   1.1.0
   ((\go ->
       (\ls -> go 42 ls)
         ((\s -> s s)
            (\s n ->
               case
                 (lessThanEqualsInteger n 0)
                 [ (constr 1 [1, ((\x -> s s x) (subtractInteger n 1))])
                 , (constr 0 []) ])
            1000))
      ((\s -> s s) (\s acc ds -> case ds [acc, (\x xs -> s s acc xs)]))))