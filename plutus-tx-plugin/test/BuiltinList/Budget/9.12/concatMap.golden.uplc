(program
   1.1.0
   ((\forced ->
       (\go xss -> go xss)
         ((\s -> s s)
            (\s xs ->
               case
                 xs
                 [ (\x ->
                      (\go xs ->
                         (\ys ->
                            (\l ->
                               (\s -> s s l)
                                 (\s xs ->
                                    case xs [(\x xs -> forced x (s s xs)), ys]))
                              (go 2))
                           (s s xs))
                        ((\s -> s s)
                           (\s n ->
                              case
                                (lessThanEqualsInteger n 0)
                                [ (forced
                                     x
                                     ((\x -> s s x) (subtractInteger n 1)))
                                , [] ])))
                 , [] ])))
      (force mkCons)))