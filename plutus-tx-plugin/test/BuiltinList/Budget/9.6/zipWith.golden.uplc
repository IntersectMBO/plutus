(program
   1.1.0
   (\xs ->
      force
        ((\cse ->
            cse
              (\x ->
                 cse
                   (\x ->
                      cse
                        (\x ->
                           (\cse -> cse (\x -> cse cse x) x)
                             (\s -> cse (\x -> s s x)))
                        x)
                   x))
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