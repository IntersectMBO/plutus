(program
   1.1.0
   ((\go xss -> go xss)
      ((\cse -> cse cse)
         (\s xs ->
            case
              xs
              [ (\x ->
                   (\go xs ->
                      (\ys ->
                         (\l ->
                            (\cse -> cse cse)
                              (\s xs ->
                                 case
                                   xs
                                   [(\x xs -> force mkCons x (s s xs)), ys])
                              l)
                           (go 2))
                        (s s xs))
                     ((\cse -> cse cse)
                        (\s n ->
                           case
                             (lessThanEqualsInteger n 0)
                             [ (force mkCons
                                  x
                                  ((\x -> s s x) (subtractInteger n 1)))
                             , [] ])))
              , [] ]))))