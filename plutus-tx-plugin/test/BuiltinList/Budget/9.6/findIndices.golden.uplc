(program
   1.1.0
   ((\go xs -> go 0 xs)
      ((\cse -> cse cse)
         (\s i xs ->
            case
              xs
              [ (\x xs ->
                   (\indices ->
                      case
                        (equalsInteger 0 (modInteger x 2))
                        [(force mkCons i indices), indices])
                     ((\x -> s s x) (addInteger 1 i) xs))
              , [] ]))))