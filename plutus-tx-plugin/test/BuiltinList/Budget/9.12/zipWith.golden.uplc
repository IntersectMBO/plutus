(program
   1.1.0
   (\xs ->
      force
        ((\f ->
            (\s -> f (\x -> f (\x -> f (\x -> f (\x -> s s x) x) x) x))
              (\s -> f (\x -> s s x)))
           (\go arg ->
              delay
                (\xs ys ->
                   case
                     xs
                     [ (\x xs' ->
                          case
                            ys
                            [ (\y ys' ->
                                 force mkCons
                                   (addInteger x y)
                                   (force (go (delay (\x -> x))) xs' ys'))
                            , [] ])
                     , [] ]))
           (delay (\x -> x)))
        xs
        xs))