(program
   1.1.0
   ((\s -> case (constr 0 [s, 0, (constr 0 [])]) [s])
      (\s i ds ->
         case
           ds
           [ (constr 1 [])
           , (\x xs ->
                case
                  (lessThanInteger x 1)
                  [ ((\x -> case (constr 0 [s, x, xs]) [s]) (addInteger 1 i))
                  , (constr 0 [i]) ]) ])))