(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [False, (\x xs -> case (lessThanInteger x 1) [(s s xs), True])])))