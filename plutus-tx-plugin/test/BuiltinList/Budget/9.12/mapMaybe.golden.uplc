(program
   1.1.0
   ((\forced xs ->
       (\s -> s s xs)
         (\s xs ->
            case
              xs
              [ (\x xs ->
                   case
                     (equalsInteger 0 (modInteger x 2))
                     [(forced x (s s xs)), (s s xs)])
              , [] ]))
      (force mkCons)))