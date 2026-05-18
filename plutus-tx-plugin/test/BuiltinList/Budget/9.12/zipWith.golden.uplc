(program
   1.1.0
   ((\forced ->
       (\go xs -> go xs xs)
         ((\s -> s s)
            (\s xs ys ->
               case
                 xs
                 [ (\x xs' ->
                      case
                        ys
                        [ (\y ys' ->
                             forced
                               (addInteger x y)
                               (case (constr 0 [s, xs', ys']) [s]))
                        , [] ])
                 , [] ])))
      (force mkCons)))