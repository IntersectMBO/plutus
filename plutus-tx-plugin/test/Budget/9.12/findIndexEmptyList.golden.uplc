(program
   1.1.0
   ((\s -> case (constr 0 [s, 0, (constr 0 [])]) [s])
      (\s i ds ->
         case
           ds
           [ (constr 1 [])
           , (\x xs ->
                case
                  (lessThanEqualsInteger 1 x)
                  [ (constr 0 [i])
                  , ((\x -> case (constr 0 [s, x, xs]) [s])
                       (addInteger 1 i)) ]) ])))