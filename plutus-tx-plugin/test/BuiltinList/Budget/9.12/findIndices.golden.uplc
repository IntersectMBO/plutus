(program
   1.1.0
   ((\go xs -> go 0 xs)
      ((\s -> s s)
         (\s i xs ->
            case
              xs
              [ (\x xs ->
                   (\indices ->
                      case
                        (equalsInteger 0 (modInteger x 2))
                        [(force mkCons i indices), indices])
                     ((\x -> case (constr 0 [s, x, xs]) [s]) (addInteger 1 i)))
              , [] ]))))