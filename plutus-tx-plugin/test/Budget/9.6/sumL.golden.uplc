(program
   1.1.0
   ((\go ->
       (\ls -> go 0 ls)
         ((\cse -> cse cse)
            (\s x lim ->
               case
                 (lessThanEqualsInteger x lim)
                 [ (constr 0 [])
                 , (constr 1 [x, ((\x -> s s x) (addInteger 1 x) lim)]) ])
            1
            1000))
      ((\cse -> cse cse)
         (\s acc ds ->
            case ds [acc, (\x xs -> (\x -> s s x) (addInteger acc x) xs)]))))