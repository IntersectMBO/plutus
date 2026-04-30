(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [ False
           , (\x xs -> case (lessThanEqualsInteger 1 x) [True, (s s xs)]) ])))