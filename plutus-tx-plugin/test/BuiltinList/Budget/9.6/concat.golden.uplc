(program
   1.1.0
   ((\go xss -> go xss)
      ((\s -> s s)
         (\s xs ->
            case
              xs
              [ (\x xs ->
                   (\acc ->
                      (\s -> s s)
                        (\s xs ->
                           case xs [(\x xs -> force mkCons x (s s xs)), acc]))
                     (s s xs)
                     x)
              , [] ]))))