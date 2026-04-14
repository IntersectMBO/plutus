(program
   1.1.0
   (\xs ->
      (\s -> s s)
        (\s xs ->
           case
             xs
             [ (\x xs ->
                  (\xs ->
                     case
                       (equalsInteger 0 (modInteger x 2))
                       [xs, (force mkCons x xs)])
                    (s s xs))
             , [] ])
        xs))