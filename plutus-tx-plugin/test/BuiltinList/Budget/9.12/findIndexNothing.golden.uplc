(program
   1.1.0
   ((\go xs -> go 0 xs)
      ((\s -> s s)
         (\s i xs ->
            case
              xs
              [ (\x xs ->
                   case
                     (equalsInteger 99 x)
                     [ ((\x -> case (constr 0 [s, x, xs]) [s]) (addInteger 1 i))
                     , (constr 0 [i]) ])
              , (constr 1 []) ]))))