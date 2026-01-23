(program
   1.1.0
   ((\go xs ->
       go
         ((\cse -> cse cse)
            (\s xs -> case xs [(\x xs -> force mkCons x (s s xs)), xs])
            xs)
         [])
      ((\cse -> cse cse)
         (\s l xs ->
            case
              l
              [ (\y ->
                   (\go ys ->
                      case
                        (go xs)
                        [ ((\cse -> cse (s s ys (cse xs))) (force mkCons y))
                        , (s s ys xs) ])
                     ((\cse -> cse cse)
                        (\s xs ->
                           case
                             xs
                             [ (\x xs ->
                                  case (equalsInteger x y) [(s s xs), True])
                             , False ])))
              , [] ]))))