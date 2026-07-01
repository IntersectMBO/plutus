(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [True, (\x xs -> case (lessThanInteger x 1) [False, (s s xs)])])))