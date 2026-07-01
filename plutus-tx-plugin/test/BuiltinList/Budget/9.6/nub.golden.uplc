(program
   1.1.0
   ((\forced ->
       (\go xs ->
          go
            ((\s -> s s xs)
               (\s xs -> case xs [(\x xs -> forced x (s s xs)), xs]))
            [])
         ((\s -> s s)
            (\s l xs ->
               case
                 l
                 [ (\y ->
                      (\go ys ->
                         case
                           (go xs)
                           [ (forced
                                y
                                (case (constr 0 [s, ys, (forced y xs)]) [s]))
                           , (case (constr 0 [s, ys, xs]) [s]) ])
                        ((\s -> s s)
                           (\s xs ->
                              case
                                xs
                                [ (\x xs ->
                                     case (equalsInteger x y) [(s s xs), True])
                                , False ])))
                 , [] ])))
      (force mkCons)))