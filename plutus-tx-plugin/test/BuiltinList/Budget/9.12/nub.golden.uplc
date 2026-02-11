(program
   1.1.0
   ((\go xs ->
       go
         ((\s -> s s)
            (\s xs -> case xs [(\x xs -> force mkCons x (s s xs)), xs])
            xs)
         [])
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
                                  case (equalsInteger x y) [(s s xs), True])
                             , False ])))
              , [] ]))))