(program
   1.1.0
   ((\forced ->
       (\go xss -> go xss)
         ((\s -> s s)
            (\s xs ->
               case
                 xs
                 [ (\x xs ->
                      (\acc ->
                         (\s -> s s x)
                           (\s xs ->
                              case xs [(\x xs -> forced x (s s xs)), acc]))
                        (s s xs))
                 , [] ])))
      (force mkCons)))