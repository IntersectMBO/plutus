(program
   1.1.0
   ((\s -> s s (constr 0 []))
      (\s ds ->
         case
           ds
           [ (constr 1 [])
           , (\x xs ->
                case
                  (lessThanEqualsInteger 1 x)
                  [(constr 0 [x]), (s s xs)]) ])))