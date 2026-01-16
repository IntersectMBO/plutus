(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds ->
         case
           ds
           [ True
           , (\x xs -> case (lessThanEqualsInteger 1 x) [(s s xs), False]) ])
      (constr 0 [])))