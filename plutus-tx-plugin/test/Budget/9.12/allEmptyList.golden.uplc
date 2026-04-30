(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [ True
           , (\x xs -> case (lessThanEqualsInteger 1 x) [(s s xs), False]) ])))