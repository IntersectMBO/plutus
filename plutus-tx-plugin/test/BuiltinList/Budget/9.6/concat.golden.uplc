(program
   1.1.0
   ((\go xss -> go xss)
      ((\cse -> cse cse)
         (\s xs ->
            case
              xs
              [ (\x xs ->
                   (\acc ->
                      (\cse -> cse cse)
                        (\s xs ->
                           case xs [(\x xs -> force mkCons x (s s xs)), acc]))
                     (s s xs)
                     x)
              , [] ]))))