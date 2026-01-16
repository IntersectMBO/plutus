(program
   1.1.0
   ((\cse -> cse cse)
      (\s ds ->
         case
           ds
           [ False
           , (\x xs -> case (lessThanEqualsInteger 1 x) [True, (s s xs)]) ])
      (constr 0 [])))