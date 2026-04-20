(program
   1.1.0
   (\xs ->
      (\s -> s s xs)
        (\s xs ->
           case
             xs
             [ (\x xs ->
                  case
                    (equalsInteger 0 (modInteger x 2))
                    [(force mkCons x (s s xs)), (s s xs)])
             , [] ])))