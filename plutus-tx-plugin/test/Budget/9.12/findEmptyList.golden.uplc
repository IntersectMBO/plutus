(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [ (constr 1 [])
           , (\x xs ->
                case (lessThanInteger x 1) [(s s xs), (constr 0 [x])]) ])))