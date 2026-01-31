(program
   1.1.0
   ((\go xs -> go xs [])
      ((\s -> s s)
         (\s l xs ->
            case
              l
              [ (\y ->
                   (\go ys ->
                      case
                        (go xs)
                        [ (force mkCons y (s s ys (force mkCons y xs)))
                        , (s s ys xs) ])
                     ((\s -> s s)
                        (\s xs ->
                           case
                             xs
                             [ (\x xs ->
                                  case
                                    (lessThanEqualsInteger x y)
                                    [(s s xs), True])
                             , False ])))
              , [] ]))))